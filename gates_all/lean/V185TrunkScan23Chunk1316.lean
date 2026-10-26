import V185TrunkScan23Chunk1315

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7793882 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2]
def baseStart_7793882 : Nat := 118140960795 + 7793882 * 2 ^ 59
def prefixEnd_7793882 : Nat := 4983230072969 + 3 ^ 40 * 7793882 * 2
def baseEnd_7793882 : Nat := 4002007630425380634531595

theorem tailTrace_7793882 : CollatzResearch.WordTrace tailWord_7793882 prefixEnd_7793882 4002007630425380634531595 := by
  unfold tailWord_7793882
  simp only [CollatzResearch.WordTrace]
  refine ⟨71066557487526019479323975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189510819966736051944863933 71066557487526019479323975)
  ·
    refine ⟨106599836231289029218985963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71066557487526019479323975 106599836231289029218985963)
    ·
      refine ⟨159899754346933543828478945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106599836231289029218985963 159899754346933543828478945)
      ·
        refine ⟨119924815760200157871359209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159899754346933543828478945 119924815760200157871359209)
        ·
          refine ⟨89943611820150118403519407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119924815760200157871359209 89943611820150118403519407)
          ·
            refine ⟨134915417730225177605279111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89943611820150118403519407 134915417730225177605279111)
            ·
              refine ⟨202373126595337766407918667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134915417730225177605279111 202373126595337766407918667)
              ·
                refine ⟨303559689893006649611878001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202373126595337766407918667 303559689893006649611878001)
                ·
                  refine ⟨227669767419754987208908501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303559689893006649611878001 227669767419754987208908501)
                  ·
                    refine ⟨5336010173900507512708793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227669767419754987208908501 5336010173900507512708793)
                    ·
                      refine ⟨4002007630425380634531595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336010173900507512708793 4002007630425380634531595)
                      ·
                        rfl

theorem cell23_7793882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_7793882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793882 prefixEnd_7793882 := by exact prefixLift 7793882
  have htrace : WordTrace (prefixWord ++ tailWord_7793882) baseStart_7793882 baseEnd_7793882 := by
    simpa [prefixWord, tailWord_7793882, baseEnd_7793882] using wordTrace_append hprefix tailTrace_7793882
  have hstable : (prefixWord ++ tailWord_7793882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793882).length < 2 ^ (prefixWord ++ tailWord_7793882).sum := by decide
  have hdescent : baseEnd_7793882 < baseStart_7793882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793893 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 1, 2, 3]
def baseStart_7793893 : Nat := 118140960795 + 7793893 * 2 ^ 59
def prefixEnd_7793893 : Nat := 4983230072969 + 3 ^ 40 * 7793893 * 2
def baseEnd_7793893 : Nat := 4002013278712580091494045

theorem tailTrace_7793893 : CollatzResearch.WordTrace tailWord_7793893 prefixEnd_7793893 4002013278712580091494045 := by
  unfold tailWord_7793893
  simp only [CollatzResearch.WordTrace]
  refine ⟨284266631153064226795946333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189511087435376151197297555 284266631153064226795946333)
  ·
    refine ⟨106599986682399085048479875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284266631153064226795946333 106599986682399085048479875)
    ·
      refine ⟨159899980023598627572719813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106599986682399085048479875 159899980023598627572719813)
      ·
        refine ⟨29981246254424742669884965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159899980023598627572719813 29981246254424742669884965)
        ·
          refine ⟨5621483672704639250603431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29981246254424742669884965 5621483672704639250603431)
          ·
            refine ⟨8432225509056958875905147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621483672704639250603431 8432225509056958875905147)
            ·
              refine ⟨12648338263585438313857721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8432225509056958875905147 12648338263585438313857721)
              ·
                refine ⟨9486253697689078735393291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12648338263585438313857721 9486253697689078735393291)
                ·
                  refine ⟨14229380546533618103089937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9486253697689078735393291 14229380546533618103089937)
                  ·
                    refine ⟨10672035409900213577317453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14229380546533618103089937 10672035409900213577317453)
                    ·
                      refine ⟨4002013278712580091494045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10672035409900213577317453 4002013278712580091494045)
                      ·
                        rfl

theorem cell23_7793893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_7793893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793893 prefixEnd_7793893 := by exact prefixLift 7793893
  have htrace : WordTrace (prefixWord ++ tailWord_7793893) baseStart_7793893 baseEnd_7793893 := by
    simpa [prefixWord, tailWord_7793893, baseEnd_7793893] using wordTrace_append hprefix tailTrace_7793893
  have hstable : (prefixWord ++ tailWord_7793893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793893).length < 2 ^ (prefixWord ++ tailWord_7793893).sum := by decide
  have hdescent : baseEnd_7793893 < baseStart_7793893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793899 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 3, 3, 2]
def baseStart_7793899 : Nat := 118140960795 + 7793899 * 2 ^ 59
def prefixEnd_7793899 : Nat := 4983230072969 + 3 ^ 40 * 7793899 * 2
def baseEnd_7793899 : Nat := 4002016359596507068019017

theorem tailTrace_7793899 : CollatzResearch.WordTrace tailWord_7793899 prefixEnd_7793899 4002016359596507068019017 := by
  unfold tailWord_7793899
  simp only [CollatzResearch.WordTrace]
  refine ⟨284266849991042489820664751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189511233327361659880443167 284266849991042489820664751)
  ·
    refine ⟨426400274986563734730997127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284266849991042489820664751 426400274986563734730997127)
    ·
      refine ⟨639600412479845602096495691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426400274986563734730997127 639600412479845602096495691)
      ·
        refine ⟨959400618719768403144743537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639600412479845602096495691 959400618719768403144743537)
        ·
          refine ⟨719550464039826302358557653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959400618719768403144743537 719550464039826302358557653)
          ·
            refine ⟨16864464000933428961528695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 719550464039826302358557653 16864464000933428961528695)
            ·
              refine ⟨25296696001400143442293043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16864464000933428961528695 25296696001400143442293043)
              ·
                refine ⟨37945044002100215163439565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25296696001400143442293043 37945044002100215163439565)
                ·
                  refine ⟨14229391500787580686289837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37945044002100215163439565 14229391500787580686289837)
                  ·
                    refine ⟨5336021812795342757358689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14229391500787580686289837 5336021812795342757358689)
                    ·
                      refine ⟨4002016359596507068019017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336021812795342757358689 4002016359596507068019017)
                      ·
                        rfl

theorem cell23_7793899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3, 2].length) (baseStart_7793899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793899 prefixEnd_7793899 := by exact prefixLift 7793899
  have htrace : WordTrace (prefixWord ++ tailWord_7793899) baseStart_7793899 baseEnd_7793899 := by
    simpa [prefixWord, tailWord_7793899, baseEnd_7793899] using wordTrace_append hprefix tailTrace_7793899
  have hstable : (prefixWord ++ tailWord_7793899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793899).length < 2 ^ (prefixWord ++ tailWord_7793899).sum := by decide
  have hdescent : baseEnd_7793899 < baseStart_7793899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793905 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 4, 6]
def baseStart_7793905 : Nat := 118140960795 + 7793905 * 2 ^ 59
def prefixEnd_7793905 : Nat := 4983230072969 + 3 ^ 40 * 7793905 * 2
def baseEnd_7793905 : Nat := 1334006480160144681514663

theorem tailTrace_7793905 : CollatzResearch.WordTrace tailWord_7793905 prefixEnd_7793905 1334006480160144681514663 := by
  unfold tailWord_7793905
  simp only [CollatzResearch.WordTrace]
  refine ⟨284267068829020752845383169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189511379219347168563588779 284267068829020752845383169)
  ·
    refine ⟨213200301621765564634037377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284267068829020752845383169 213200301621765564634037377)
    ·
      refine ⟨159900226216324173475528033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213200301621765564634037377 159900226216324173475528033)
      ·
        refine ⟨119925169662243130106646025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159900226216324173475528033 119925169662243130106646025)
        ·
          refine ⟨89943877246682347579984519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119925169662243130106646025 89943877246682347579984519)
          ·
            refine ⟨134915815870023521369976779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89943877246682347579984519 134915815870023521369976779)
            ·
              refine ⟨202373723805035282054965169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134915815870023521369976779 202373723805035282054965169)
              ·
                refine ⟨151780292853776461541223877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202373723805035282054965169 151780292853776461541223877)
                ·
                  refine ⟨28458804910083086538979477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151780292853776461541223877 28458804910083086538979477)
                  ·
                    refine ⟨1334006480160144681514663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28458804910083086538979477 1334006480160144681514663)
                    ·
                      rfl

theorem cell23_7793905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_7793905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793905 prefixEnd_7793905 := by exact prefixLift 7793905
  have htrace : WordTrace (prefixWord ++ tailWord_7793905) baseStart_7793905 baseEnd_7793905 := by
    simpa [prefixWord, tailWord_7793905, baseEnd_7793905] using wordTrace_append hprefix tailTrace_7793905
  have hstable : (prefixWord ++ tailWord_7793905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793905).length < 2 ^ (prefixWord ++ tailWord_7793905).sum := by decide
  have hdescent : baseEnd_7793905 < baseStart_7793905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793932 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_7793932 : Nat := 118140960795 + 7793932 * 2 ^ 59
def prefixEnd_7793932 : Nat := 4983230072969 + 3 ^ 40 * 7793932 * 2
def baseEnd_7793932 : Nat := 4002033304458105438906365

theorem tailTrace_7793932 : CollatzResearch.WordTrace tailWord_7793932 prefixEnd_7793932 4002033304458105438906365 := by
  unfold tailWord_7793932
  simp only [CollatzResearch.WordTrace]
  refine ⟨142134026799961468228308025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189512035733281957637744033 142134026799961468228308025)
  ·
    refine ⟨106600520099971101171231019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142134026799961468228308025 106600520099971101171231019)
    ·
      refine ⟨159900780149956651756846529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106600520099971101171231019 159900780149956651756846529)
      ·
        refine ⟨119925585112467488817634897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159900780149956651756846529 119925585112467488817634897)
        ·
          refine ⟨89944188834350616613226173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119925585112467488817634897 89944188834350616613226173)
          ·
            refine ⟨33729070812881481229959815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89944188834350616613226173 33729070812881481229959815)
            ·
              refine ⟨50593606219322221844939723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33729070812881481229959815 50593606219322221844939723)
              ·
                refine ⟨75890409328983332767409585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50593606219322221844939723 75890409328983332767409585)
                ·
                  refine ⟨56917806996737499575557189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75890409328983332767409585 56917806996737499575557189)
                  ·
                    refine ⟨10672088811888281170416973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56917806996737499575557189 10672088811888281170416973)
                    ·
                      refine ⟨4002033304458105438906365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10672088811888281170416973 4002033304458105438906365)
                      ·
                        rfl

theorem cell23_7793932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_7793932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793932 prefixEnd_7793932 := by exact prefixLift 7793932
  have htrace : WordTrace (prefixWord ++ tailWord_7793932) baseStart_7793932 baseEnd_7793932 := by
    simpa [prefixWord, tailWord_7793932, baseEnd_7793932] using wordTrace_append hprefix tailTrace_7793932
  have hstable : (prefixWord ++ tailWord_7793932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793932).length < 2 ^ (prefixWord ++ tailWord_7793932).sum := by decide
  have hdescent : baseEnd_7793932 < baseStart_7793932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793946 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2]
def baseStart_7793946 : Nat := 118140960795 + 7793946 * 2 ^ 59
def prefixEnd_7793946 : Nat := 4983230072969 + 3 ^ 40 * 7793946 * 2
def baseEnd_7793946 : Nat := 4002040493187268384131301

theorem tailTrace_7793946 : CollatzResearch.WordTrace tailWord_7793946 prefixEnd_7793946 4002040493187268384131301 := by
  unfold tailWord_7793946
  simp only [CollatzResearch.WordTrace]
  refine ⟨71067141055468054211906423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189512376147914811231750461 71067141055468054211906423)
  ·
    refine ⟨106600711583202081317859635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71067141055468054211906423 106600711583202081317859635)
    ·
      refine ⟨159901067374803121976789453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106600711583202081317859635 159901067374803121976789453)
      ·
        refine ⟨59962900265551170741296045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159901067374803121976789453 59962900265551170741296045)
        ·
          refine ⟨22486087599581689027986017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59962900265551170741296045 22486087599581689027986017)
          ·
            refine ⟨16864565699686266770989513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22486087599581689027986017 16864565699686266770989513)
            ·
              refine ⟨12648424274764700078242135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16864565699686266770989513 12648424274764700078242135)
              ·
                refine ⟨18972636412147050117363203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12648424274764700078242135 18972636412147050117363203)
                ·
                  refine ⟨28458954618220575176044805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18972636412147050117363203 28458954618220575176044805)
                  ·
                    refine ⟨5336053990916357845508401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28458954618220575176044805 5336053990916357845508401)
                    ·
                      refine ⟨4002040493187268384131301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336053990916357845508401 4002040493187268384131301)
                      ·
                        rfl

theorem cell23_7793946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_7793946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793946 prefixEnd_7793946 := by exact prefixLift 7793946
  have htrace : WordTrace (prefixWord ++ tailWord_7793946) baseStart_7793946 baseEnd_7793946 := by
    simpa [prefixWord, tailWord_7793946, baseEnd_7793946] using wordTrace_append hprefix tailTrace_7793946
  have hstable : (prefixWord ++ tailWord_7793946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793946).length < 2 ^ (prefixWord ++ tailWord_7793946).sum := by decide
  have hdescent : baseEnd_7793946 < baseStart_7793946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793969 : List Nat := [1, 2, 2, 3, 3, 1, 1, 5, 5]
def baseStart_7793969 : Nat := 118140960795 + 7793969 * 2 ^ 59
def prefixEnd_7793969 : Nat := 4983230072969 + 3 ^ 40 * 7793969 * 2
def baseEnd_7793969 : Nat := 444672478138035754904855

theorem tailTrace_7793969 : CollatzResearch.WordTrace tailWord_7793969 prefixEnd_7793969 444672478138035754904855 := by
  unfold tailWord_7793969
  simp only [CollatzResearch.WordTrace]
  refine ⟨284269403100788891775712961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189512935400525927850475307 284269403100788891775712961)
  ·
    refine ⟨213202052325591668831784721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284269403100788891775712961 213202052325591668831784721)
    ·
      refine ⟨159901539244193751623838541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213202052325591668831784721 159901539244193751623838541)
      ·
        refine ⟨59963077216572656858939453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159901539244193751623838541 59963077216572656858939453)
        ·
          refine ⟨22486153956214746322102295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59963077216572656858939453 22486153956214746322102295)
          ·
            refine ⟨33729230934322119483153443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22486153956214746322102295 33729230934322119483153443)
            ·
              refine ⟨50593846401483179224730165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33729230934322119483153443 50593846401483179224730165)
              ·
                refine ⟨4743173100139048052318453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50593846401483179224730165 4743173100139048052318453)
                ·
                  refine ⟨444672478138035754904855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4743173100139048052318453 444672478138035754904855)
                  ·
                    rfl

theorem cell23_7793969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 5].length) (baseStart_7793969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793969 prefixEnd_7793969 := by exact prefixLift 7793969
  have htrace : WordTrace (prefixWord ++ tailWord_7793969) baseStart_7793969 baseEnd_7793969 := by
    simpa [prefixWord, tailWord_7793969, baseEnd_7793969] using wordTrace_append hprefix tailTrace_7793969
  have hstable : (prefixWord ++ tailWord_7793969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793969).length < 2 ^ (prefixWord ++ tailWord_7793969).sum := by decide
  have hdescent : baseEnd_7793969 < baseStart_7793969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7793997 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_7793997 : Nat := 118140960795 + 7793997 * 2 ^ 59
def prefixEnd_7793997 : Nat := 4983230072969 + 3 ^ 40 * 7793997 * 2
def baseEnd_7793997 : Nat := 4002066680700647684593567

theorem tailTrace_7793997 : CollatzResearch.WordTrace tailWord_7793997 prefixEnd_7793997 4002066680700647684593567 := by
  unfold tailWord_7793997
  simp only [CollatzResearch.WordTrace]
  refine ⟨284270424344687452557732245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189513616229791635038488163 284270424344687452557732245)
  ·
    refine ⟨13325176141157224338643699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 284270424344687452557732245 13325176141157224338643699)
    ·
      refine ⟨19987764211735836507965549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13325176141157224338643699 19987764211735836507965549)
      ·
        refine ⟨7495411579400938690487081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19987764211735836507965549 7495411579400938690487081)
        ·
          refine ⟨5621558684550704017865311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7495411579400938690487081 5621558684550704017865311)
          ·
            refine ⟨8432338026826056026797967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621558684550704017865311 8432338026826056026797967)
            ·
              refine ⟨12648507040239084040196951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8432338026826056026797967 12648507040239084040196951)
              ·
                refine ⟨18972760560358626060295427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12648507040239084040196951 18972760560358626060295427)
                ·
                  refine ⟨28459140840537939090443141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18972760560358626060295427 28459140840537939090443141)
                  ·
                    refine ⟨5336088907600863579458089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28459140840537939090443141 5336088907600863579458089)
                    ·
                      refine ⟨4002066680700647684593567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336088907600863579458089 4002066680700647684593567)
                      ·
                        rfl

theorem cell23_7793997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_7793997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7793997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7793997 prefixEnd_7793997 := by exact prefixLift 7793997
  have htrace : WordTrace (prefixWord ++ tailWord_7793997) baseStart_7793997 baseEnd_7793997 := by
    simpa [prefixWord, tailWord_7793997, baseEnd_7793997] using wordTrace_append hprefix tailTrace_7793997
  have hstable : (prefixWord ++ tailWord_7793997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7793997).length < 2 ^ (prefixWord ++ tailWord_7793997).sum := by decide
  have hdescent : baseEnd_7793997 < baseStart_7793997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7793997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794039 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_7794039 : Nat := 118140960795 + 7794039 * 2 ^ 59
def prefixEnd_7794039 : Nat := 4983230072969 + 3 ^ 40 * 7794039 * 2
def baseEnd_7794039 : Nat := 4002088246888136520268373

theorem tailTrace_7794039 : CollatzResearch.WordTrace tailWord_7794039 prefixEnd_7794039 4002088246888136520268373 := by
  unfold tailWord_7794039
  simp only [CollatzResearch.WordTrace]
  refine ⟨284271956210535293730761171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189514637473690195820507447 284271956210535293730761171)
  ·
    refine ⟨426407934315802940596141757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284271956210535293730761171 426407934315802940596141757)
    ·
      refine ⟨159902975368426102723553159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426407934315802940596141757 159902975368426102723553159)
      ·
        refine ⟨239854463052639154085329739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159902975368426102723553159 239854463052639154085329739)
        ·
          refine ⟨359781694578958731127994609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239854463052639154085329739 359781694578958731127994609)
          ·
            refine ⟨269836270934219048345995957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359781694578958731127994609 269836270934219048345995957)
            ·
              refine ⟨25297150400083035782437121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269836270934219048345995957 25297150400083035782437121)
              ·
                refine ⟨18972862800062276836827841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25297150400083035782437121 18972862800062276836827841)
                ·
                  refine ⟨14229647100046707627620881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18972862800062276836827841 14229647100046707627620881)
                  ·
                    refine ⟨10672235325035030720715661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14229647100046707627620881 10672235325035030720715661)
                    ·
                      refine ⟨4002088246888136520268373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10672235325035030720715661 4002088246888136520268373)
                      ·
                        rfl

theorem cell23_7794039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_7794039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794039 prefixEnd_7794039 := by exact prefixLift 7794039
  have htrace : WordTrace (prefixWord ++ tailWord_7794039) baseStart_7794039 baseEnd_7794039 := by
    simpa [prefixWord, tailWord_7794039, baseEnd_7794039] using wordTrace_append hprefix tailTrace_7794039
  have hstable : (prefixWord ++ tailWord_7794039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794039).length < 2 ^ (prefixWord ++ tailWord_7794039).sum := by decide
  have hdescent : baseEnd_7794039 < baseStart_7794039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794103 : List Nat := [1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 3]
def baseStart_7794103 : Nat := 118140960795 + 7794103 * 2 ^ 59
def prefixEnd_7794103 : Nat := 4983230072969 + 3 ^ 40 * 7794103 * 2
def baseEnd_7794103 : Nat := 4002121109650024269868079

theorem tailTrace_7794103 : CollatzResearch.WordTrace tailWord_7794103 prefixEnd_7794103 4002121109650024269868079 := by
  unfold tailWord_7794103
  simp only [CollatzResearch.WordTrace]
  refine ⟨284274290482303432661090963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189516193654868955107393975 284274290482303432661090963)
  ·
    refine ⟨426411435723455148991636445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284274290482303432661090963 426411435723455148991636445)
    ·
      refine ⟨159904288396295680871863667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426411435723455148991636445 159904288396295680871863667)
      ·
        refine ⟨239856432594443521307795501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159904288396295680871863667 239856432594443521307795501)
        ·
          refine ⟨89946162222916320490423313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239856432594443521307795501 89946162222916320490423313)
          ·
            refine ⟨67459621667187240367817485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89946162222916320490423313 67459621667187240367817485)
            ·
              refine ⟨25297358125195215137931557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67459621667187240367817485 25297358125195215137931557)
              ·
                refine ⟨4743254648474102838362167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25297358125195215137931557 4743254648474102838362167)
                ·
                  refine ⟨7114881972711154257543251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743254648474102838362167 7114881972711154257543251)
                  ·
                    refine ⟨10672322959066731386314877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7114881972711154257543251 10672322959066731386314877)
                    ·
                      refine ⟨4002121109650024269868079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10672322959066731386314877 4002121109650024269868079)
                      ·
                        rfl

theorem cell23_7794103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_7794103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794103 prefixEnd_7794103 := by exact prefixLift 7794103
  have htrace : WordTrace (prefixWord ++ tailWord_7794103) baseStart_7794103 baseEnd_7794103 := by
    simpa [prefixWord, tailWord_7794103, baseEnd_7794103] using wordTrace_append hprefix tailTrace_7794103
  have hstable : (prefixWord ++ tailWord_7794103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794103).length < 2 ^ (prefixWord ++ tailWord_7794103).sum := by decide
  have hdescent : baseEnd_7794103 < baseStart_7794103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794109 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7794109 : Nat := 118140960795 + 7794109 * 2 ^ 59
def prefixEnd_7794109 : Nat := 4983230072969 + 3 ^ 40 * 7794109 * 2
def baseEnd_7794109 : Nat := 4002124190533951246393051

theorem tailTrace_7794109 : CollatzResearch.WordTrace tailWord_7794109 prefixEnd_7794109 4002124190533951246393051 := by
  unfold tailWord_7794109
  simp only [CollatzResearch.WordTrace]
  refine ⟨284274509320281695685809381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189516339546854463790539587 284274509320281695685809381)
  ·
    refine ⟨53301470497552817941089259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284274509320281695685809381 53301470497552817941089259)
    ·
      refine ⟨79952205746329226911633889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53301470497552817941089259 79952205746329226911633889)
      ·
        refine ⟨59964154309746920183725417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79952205746329226911633889 59964154309746920183725417)
        ·
          refine ⟨44973115732310190137794063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59964154309746920183725417 44973115732310190137794063)
          ·
            refine ⟨67459673598465285206691095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44973115732310190137794063 67459673598465285206691095)
            ·
              refine ⟨101189510397697927810036643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67459673598465285206691095 101189510397697927810036643)
              ·
                refine ⟨151784265596546891715054965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101189510397697927810036643 151784265596546891715054965)
                ·
                  refine ⟨14229774899676271098286403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151784265596546891715054965 14229774899676271098286403)
                  ·
                    refine ⟨21344662349514406647429605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14229774899676271098286403 21344662349514406647429605)
                    ·
                      refine ⟨4002124190533951246393051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21344662349514406647429605 4002124190533951246393051)
                      ·
                        rfl

theorem cell23_7794109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7794109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794109 prefixEnd_7794109 := by exact prefixLift 7794109
  have htrace : WordTrace (prefixWord ++ tailWord_7794109) baseStart_7794109 baseEnd_7794109 := by
    simpa [prefixWord, tailWord_7794109, baseEnd_7794109] using wordTrace_append hprefix tailTrace_7794109
  have hstable : (prefixWord ++ tailWord_7794109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794109).length < 2 ^ (prefixWord ++ tailWord_7794109).sum := by decide
  have hdescent : baseEnd_7794109 < baseStart_7794109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794119 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 1, 6]
def baseStart_7794119 : Nat := 118140960795 + 7794119 * 2 ^ 59
def prefixEnd_7794119 : Nat := 4983230072969 + 3 ^ 40 * 7794119 * 2
def baseEnd_7794119 : Nat := 1334043108446832069089335

theorem tailTrace_7794119 : CollatzResearch.WordTrace tailWord_7794119 prefixEnd_7794119 1334043108446832069089335 := by
  unfold tailWord_7794119
  simp only [CollatzResearch.WordTrace]
  refine ⟨284274874050245467393673411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189516582700163644929115607 284274874050245467393673411)
  ·
    refine ⟨426412311075368201090510117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284274874050245467393673411 426412311075368201090510117)
    ·
      refine ⟨79952308326631537704470647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426412311075368201090510117 79952308326631537704470647)
      ·
        refine ⟨119928462489947306556705971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79952308326631537704470647 119928462489947306556705971)
        ·
          refine ⟨179892693734920959835058957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119928462489947306556705971 179892693734920959835058957)
          ·
            refine ⟨67459760150595359938147109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179892693734920959835058957 67459760150595359938147109)
            ·
              refine ⟨12648705028236629988402583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67459760150595359938147109 12648705028236629988402583)
              ·
                refine ⟨18973057542354944982603875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12648705028236629988402583 18973057542354944982603875)
                ·
                  refine ⟨28459586313532417473905813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18973057542354944982603875 28459586313532417473905813)
                  ·
                    refine ⟨1334043108446832069089335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28459586313532417473905813 1334043108446832069089335)
                    ·
                      rfl

theorem cell23_7794119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_7794119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794119 prefixEnd_7794119 := by exact prefixLift 7794119
  have htrace : WordTrace (prefixWord ++ tailWord_7794119) baseStart_7794119 baseEnd_7794119 := by
    simpa [prefixWord, tailWord_7794119, baseEnd_7794119] using wordTrace_append hprefix tailTrace_7794119
  have hstable : (prefixWord ++ tailWord_7794119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794119).length < 2 ^ (prefixWord ++ tailWord_7794119).sum := by decide
  have hdescent : baseEnd_7794119 < baseStart_7794119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794149 : List Nat := [1, 3, 1, 5, 1, 2, 10]
def baseStart_7794149 : Nat := 118140960795 + 7794149 * 2 ^ 59
def prefixEnd_7794149 : Nat := 4983230072969 + 3 ^ 40 * 7794149 * 2
def baseEnd_7794149 : Nat := 49409194194569519628307

theorem tailTrace_7794149 : CollatzResearch.WordTrace tailWord_7794149 prefixEnd_7794149 49409194194569519628307 := by
  unfold tailWord_7794149
  simp only [CollatzResearch.WordTrace]
  refine ⟨284275968240136782517265501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189517312160091188344843667 284275968240136782517265501)
  ·
    refine ⟨106603488090051293443974563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284275968240136782517265501 106603488090051293443974563)
    ·
      refine ⟨159905232135076940165961845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106603488090051293443974563 159905232135076940165961845)
      ·
        refine ⟨14991115512663463140558923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159905232135076940165961845 14991115512663463140558923)
        ·
          refine ⟨22486673268995194710838385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14991115512663463140558923 22486673268995194710838385)
          ·
            refine ⟨16865004951746396033128789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22486673268995194710838385 16865004951746396033128789)
            ·
              refine ⟨49409194194569519628307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16865004951746396033128789 49409194194569519628307)
              ·
                rfl

theorem cell23_7794149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 10].length) (baseStart_7794149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794149 prefixEnd_7794149 := by exact prefixLift 7794149
  have htrace : WordTrace (prefixWord ++ tailWord_7794149) baseStart_7794149 baseEnd_7794149 := by
    simpa [prefixWord, tailWord_7794149, baseEnd_7794149] using wordTrace_append hprefix tailTrace_7794149
  have hstable : (prefixWord ++ tailWord_7794149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794149).length < 2 ^ (prefixWord ++ tailWord_7794149).sum := by decide
  have hdescent : baseEnd_7794149 < baseStart_7794149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794159 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_7794159 : Nat := 118140960795 + 7794159 * 2 ^ 59
def prefixEnd_7794159 : Nat := 4983230072969 + 3 ^ 40 * 7794159 * 2
def baseEnd_7794159 : Nat := 4002149864566676050767821

theorem tailTrace_7794159 : CollatzResearch.WordTrace tailWord_7794159 prefixEnd_7794159 4002149864566676050767821 := by
  unfold tailWord_7794159
  simp only [CollatzResearch.WordTrace]
  refine ⟨284276332970100554225129531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189517555313400369483419687 284276332970100554225129531)
  ·
    refine ⟨426414499455150831337694297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284276332970100554225129531 426414499455150831337694297)
    ·
      refine ⟨319810874591363123503270723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426414499455150831337694297 319810874591363123503270723)
      ·
        refine ⟨479716311887044685254906085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319810874591363123503270723 479716311887044685254906085)
        ·
          refine ⟨89946808478820878485294891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 479716311887044685254906085 89946808478820878485294891)
          ·
            refine ⟨134920212718231317727942337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89946808478820878485294891 134920212718231317727942337)
            ·
              refine ⟨101190159538673488295956753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134920212718231317727942337 101190159538673488295956753)
              ·
                refine ⟨75892619654005116221967565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101190159538673488295956753 75892619654005116221967565)
                ·
                  refine ⟨28459732370251918583237837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75892619654005116221967565 28459732370251918583237837)
                  ·
                    refine ⟨10672399638844469468714189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28459732370251918583237837 10672399638844469468714189)
                    ·
                      refine ⟨4002149864566676050767821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10672399638844469468714189 4002149864566676050767821)
                      ·
                        rfl

theorem cell23_7794159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_7794159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794159 prefixEnd_7794159 := by exact prefixLift 7794159
  have htrace : WordTrace (prefixWord ++ tailWord_7794159) baseStart_7794159 baseEnd_7794159 := by
    simpa [prefixWord, tailWord_7794159, baseEnd_7794159] using wordTrace_append hprefix tailTrace_7794159
  have hstable : (prefixWord ++ tailWord_7794159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794159).length < 2 ^ (prefixWord ++ tailWord_7794159).sum := by decide
  have hdescent : baseEnd_7794159 < baseStart_7794159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794160 : List Nat := [2, 1, 1, 1, 3, 4, 2, 4, 1, 2, 2]
def baseStart_7794160 : Nat := 118140960795 + 7794160 * 2 ^ 59
def prefixEnd_7794160 : Nat := 4983230072969 + 3 ^ 40 * 7794160 * 2
def baseEnd_7794160 : Nat := 4002150378047330546855317

theorem tailTrace_7794160 : CollatzResearch.WordTrace tailWord_7794160 prefixEnd_7794160 4002150378047330546855317 := by
  unfold tailWord_7794160
  simp only [CollatzResearch.WordTrace]
  refine ⟨142138184721548465697957967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189517579628731287597277289 142138184721548465697957967)
  ·
    refine ⟨213207277082322698546936951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142138184721548465697957967 213207277082322698546936951)
    ·
      refine ⟨319810915623484047820405427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213207277082322698546936951 319810915623484047820405427)
      ·
        refine ⟨479716373435226071730608141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319810915623484047820405427 479716373435226071730608141)
        ·
          refine ⟨179893640038209776898978053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479716373435226071730608141 179893640038209776898978053)
          ·
            refine ⟨33730057507164333168558385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179893640038209776898978053 33730057507164333168558385)
            ·
              refine ⟨25297543130373249876418789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33730057507164333168558385 25297543130373249876418789)
              ·
                refine ⟨4743289336944984351828523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25297543130373249876418789 4743289336944984351828523)
                ·
                  refine ⟨7114934005417476527742785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743289336944984351828523 7114934005417476527742785)
                  ·
                    refine ⟨5336200504063107395807089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7114934005417476527742785 5336200504063107395807089)
                    ·
                      refine ⟨4002150378047330546855317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336200504063107395807089 4002150378047330546855317)
                      ·
                        rfl

theorem cell23_7794160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 2, 2].length) (baseStart_7794160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794160 prefixEnd_7794160 := by exact prefixLift 7794160
  have htrace : WordTrace (prefixWord ++ tailWord_7794160) baseStart_7794160 baseEnd_7794160 := by
    simpa [prefixWord, tailWord_7794160, baseEnd_7794160] using wordTrace_append hprefix tailTrace_7794160
  have hstable : (prefixWord ++ tailWord_7794160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794160).length < 2 ^ (prefixWord ++ tailWord_7794160).sum := by decide
  have hdescent : baseEnd_7794160 < baseStart_7794160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794180 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7794180 : Nat := 118140960795 + 7794180 * 2 ^ 59
def prefixEnd_7794180 : Nat := 4983230072969 + 3 ^ 40 * 7794180 * 2
def baseEnd_7794180 : Nat := 4002160647660420468605225

theorem tailTrace_7794180 : CollatzResearch.WordTrace tailWord_7794180 prefixEnd_7794180 4002160647660420468605225 := by
  unfold tailWord_7794180
  simp only [CollatzResearch.WordTrace]
  refine ⟨142138549451512237405821997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189518065935349649874429329 142138549451512237405821997)
  ·
    refine ⟨53301956044317089027183249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142138549451512237405821997 53301956044317089027183249)
    ·
      refine ⟨39976467033237816770387437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53301956044317089027183249 39976467033237816770387437)
      ·
        refine ⟨14991175137464181288895289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39976467033237816770387437 14991175137464181288895289)
        ·
          refine ⟨11243381353098135966671467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14991175137464181288895289 11243381353098135966671467)
          ·
            refine ⟨16865072029647203950007201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243381353098135966671467 16865072029647203950007201)
            ·
              refine ⟨12648804022235402962505401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16865072029647203950007201 12648804022235402962505401)
              ·
                refine ⟨9486603016676552221879051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12648804022235402962505401 9486603016676552221879051)
                ·
                  refine ⟨14229904525014828332818577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9486603016676552221879051 14229904525014828332818577)
                  ·
                    refine ⟨10672428393761121249613933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14229904525014828332818577 10672428393761121249613933)
                    ·
                      refine ⟨4002160647660420468605225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10672428393761121249613933 4002160647660420468605225)
                      ·
                        rfl

theorem cell23_7794180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7794180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794180 prefixEnd_7794180 := by exact prefixLift 7794180
  have htrace : WordTrace (prefixWord ++ tailWord_7794180) baseStart_7794180 baseEnd_7794180 := by
    simpa [prefixWord, tailWord_7794180, baseEnd_7794180] using wordTrace_append hprefix tailTrace_7794180
  have hstable : (prefixWord ++ tailWord_7794180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794180).length < 2 ^ (prefixWord ++ tailWord_7794180).sum := by decide
  have hdescent : baseEnd_7794180 < baseStart_7794180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794237 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7794237 : Nat := 118140960795 + 7794237 * 2 ^ 59
def prefixEnd_7794237 : Nat := 4983230072969 + 3 ^ 40 * 7794237 * 2
def baseEnd_7794237 : Nat := 4002189916057726745592463

theorem tailTrace_7794237 : CollatzResearch.WordTrace tailWord_7794237 prefixEnd_7794237 4002189916057726745592463 := by
  unfold tailWord_7794237
  simp only [CollatzResearch.WordTrace]
  refine ⟨284279177863817973546468965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189519451909211982364312643 284279177863817973546468965)
  ·
    refine ⟨53302345849465870039962931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284279177863817973546468965 53302345849465870039962931)
    ·
      refine ⟨79953518774198805059944397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53302345849465870039962931 79953518774198805059944397)
      ·
        refine ⟨29982569540324551897479149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79953518774198805059944397 29982569540324551897479149)
        ·
          refine ⟨11243463577621706961554681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29982569540324551897479149 11243463577621706961554681)
          ·
            refine ⟨8432597683216280221166011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11243463577621706961554681 8432597683216280221166011)
            ·
              refine ⟨12648896524824420331749017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8432597683216280221166011 12648896524824420331749017)
              ·
                refine ⟨9486672393618315248811763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12648896524824420331749017 9486672393618315248811763)
                ·
                  refine ⟨14230008590427472873217645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9486672393618315248811763 14230008590427472873217645)
                  ·
                    refine ⟨5336253221410302327456617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14230008590427472873217645 5336253221410302327456617)
                    ·
                      refine ⟨4002189916057726745592463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336253221410302327456617 4002189916057726745592463)
                      ·
                        rfl

theorem cell23_7794237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7794237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794237 prefixEnd_7794237 := by exact prefixLift 7794237
  have htrace : WordTrace (prefixWord ++ tailWord_7794237) baseStart_7794237 baseEnd_7794237 := by
    simpa [prefixWord, tailWord_7794237, baseEnd_7794237] using wordTrace_append hprefix tailTrace_7794237
  have hstable : (prefixWord ++ tailWord_7794237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794237).length < 2 ^ (prefixWord ++ tailWord_7794237).sum := by decide
  have hdescent : baseEnd_7794237 < baseStart_7794237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794256 : List Nat := [2, 1, 1, 1, 1, 3, 4, 5, 5]
def baseStart_7794256 : Nat := 118140960795 + 7794256 * 2 ^ 59
def prefixEnd_7794256 : Nat := 4983230072969 + 3 ^ 40 * 7794256 * 2
def baseEnd_7794256 : Nat := 444688852465573574583875

theorem tailTrace_7794256 : CollatzResearch.WordTrace tailWord_7794256 prefixEnd_7794256 444688852465573574583875 := by
  unfold tailWord_7794256
  simp only [CollatzResearch.WordTrace]
  refine ⟨142139935425374569895705311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189519913900499426527607081 142139935425374569895705311)
  ·
    refine ⟨213209903138061854843557967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142139935425374569895705311 213209903138061854843557967)
    ·
      refine ⟨319814854707092782265336951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213209903138061854843557967 319814854707092782265336951)
      ·
        refine ⟨479722282060639173398005427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319814854707092782265336951 479722282060639173398005427)
        ·
          refine ⟨719583423090958760097008141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479722282060639173398005427 719583423090958760097008141)
          ·
            refine ⟨269843783659109535036378053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 719583423090958760097008141 269843783659109535036378053)
            ·
              refine ⟨50595709436083037819320885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269843783659109535036378053 50595709436083037819320885)
              ·
                refine ⟨4743347759632784795561333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50595709436083037819320885 4743347759632784795561333)
                ·
                  refine ⟨444688852465573574583875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4743347759632784795561333 444688852465573574583875)
                  ·
                    rfl

theorem cell23_7794256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 5].length) (baseStart_7794256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794256 prefixEnd_7794256 := by exact prefixLift 7794256
  have htrace : WordTrace (prefixWord ++ tailWord_7794256) baseStart_7794256 baseEnd_7794256 := by
    simpa [prefixWord, tailWord_7794256, baseEnd_7794256] using wordTrace_append hprefix tailTrace_7794256
  have hstable : (prefixWord ++ tailWord_7794256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794256).length < 2 ^ (prefixWord ++ tailWord_7794256).sum := by decide
  have hdescent : baseEnd_7794256 < baseStart_7794256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794316 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_7794316 : Nat := 118140960795 + 7794316 * 2 ^ 59
def prefixEnd_7794316 : Nat := 4983230072969 + 3 ^ 40 * 7794316 * 2
def baseEnd_7794316 : Nat := 1334076827009810645501533

theorem tailTrace_7794316 : CollatzResearch.WordTrace tailWord_7794316 prefixEnd_7794316 1334076827009810645501533 := by
  unfold tailWord_7794316
  simp only [CollatzResearch.WordTrace]
  refine ⟨142141029615265885019297401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189521372820354513359063201 142141029615265885019297401)
  ·
    refine ⟨106605772211449413764473051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142141029615265885019297401 106605772211449413764473051)
    ·
      refine ⟨159908658317174120646709577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106605772211449413764473051 159908658317174120646709577)
      ·
        refine ⟨119931493737880590485032183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159908658317174120646709577 119931493737880590485032183)
        ·
          refine ⟨179897240606820885727548275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119931493737880590485032183 179897240606820885727548275)
          ·
            refine ⟨269845860910231328591322413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179897240606820885727548275 269845860910231328591322413)
            ·
              refine ⟨101192197841336748221745905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269845860910231328591322413 101192197841336748221745905)
              ·
                refine ⟨75894148381002561166309429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101192197841336748221745905 75894148381002561166309429)
                ·
                  refine ⟨7115076410718990109341509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75894148381002561166309429 7115076410718990109341509)
                  ·
                    refine ⟨1334076827009810645501533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7115076410718990109341509 1334076827009810645501533)
                    ·
                      rfl

theorem cell23_7794316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_7794316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794316 prefixEnd_7794316 := by exact prefixLift 7794316
  have htrace : WordTrace (prefixWord ++ tailWord_7794316) baseStart_7794316 baseEnd_7794316 := by
    simpa [prefixWord, tailWord_7794316, baseEnd_7794316] using wordTrace_append hprefix tailTrace_7794316
  have hstable : (prefixWord ++ tailWord_7794316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794316).length < 2 ^ (prefixWord ++ tailWord_7794316).sum := by decide
  have hdescent : baseEnd_7794316 < baseStart_7794316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794433 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_7794433 : Nat := 118140960795 + 7794433 * 2 ^ 59
def prefixEnd_7794433 : Nat := 4983230072969 + 3 ^ 40 * 7794433 * 2
def baseEnd_7794433 : Nat := 4002290558266007978741561

theorem tailTrace_7794433 : CollatzResearch.WordTrace tailWord_7794433 prefixEnd_7794433 4002290558266007978741561 := by
  unfold tailWord_7794433
  simp only [CollatzResearch.WordTrace]
  refine ⟨284286326571107899020603953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189524217714071932680402635 284286326571107899020603953)
  ·
    refine ⟨213214744928330924265452965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284286326571107899020603953 213214744928330924265452965)
    ·
      refine ⟨39977764674062048299772431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213214744928330924265452965 39977764674062048299772431)
      ·
        refine ⟨59966647011093072449658647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39977764674062048299772431 59966647011093072449658647)
        ·
          refine ⟨89949970516639608674487971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59966647011093072449658647 89949970516639608674487971)
          ·
            refine ⟨134924955774959413011731957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89949970516639608674487971 134924955774959413011731957)
            ·
              refine ⟨12649214603902444969849871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134924955774959413011731957 12649214603902444969849871)
              ·
                refine ⟨18973821905853667454774807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12649214603902444969849871 18973821905853667454774807)
                ·
                  refine ⟨28460732858780501182162211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18973821905853667454774807 28460732858780501182162211)
                  ·
                    refine ⟨42691099288170751773243317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28460732858780501182162211 42691099288170751773243317)
                    ·
                      refine ⟨4002290558266007978741561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42691099288170751773243317 4002290558266007978741561)
                      ·
                        rfl

theorem cell23_7794433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_7794433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794433 prefixEnd_7794433 := by exact prefixLift 7794433
  have htrace : WordTrace (prefixWord ++ tailWord_7794433) baseStart_7794433 baseEnd_7794433 := by
    simpa [prefixWord, tailWord_7794433, baseEnd_7794433] using wordTrace_append hprefix tailTrace_7794433
  have hstable : (prefixWord ++ tailWord_7794433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794433).length < 2 ^ (prefixWord ++ tailWord_7794433).sum := by decide
  have hdescent : baseEnd_7794433 < baseStart_7794433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794436 : List Nat := [2, 3, 2, 2, 1, 13]
def baseStart_7794436 : Nat := 118140960795 + 7794436 * 2 ^ 59
def prefixEnd_7794436 : Nat := 4983230072969 + 3 ^ 40 * 7794436 * 2
def baseEnd_7794436 : Nat := 16470337854765314679029

theorem tailTrace_7794436 : CollatzResearch.WordTrace tailWord_7794436 prefixEnd_7794436 16470337854765314679029 := by
  unfold tailWord_7794436
  simp only [CollatzResearch.WordTrace]
  refine ⟨142143217995048515266481581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189524290660064687021975441 142143217995048515266481581)
  ·
    refine ⟨53303706748143193224930593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142143217995048515266481581 53303706748143193224930593)
    ·
      refine ⟨39977780061107394918697945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53303706748143193224930593 39977780061107394918697945)
      ·
        refine ⟨29983335045830546189023459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39977780061107394918697945 29983335045830546189023459)
        ·
          refine ⟨44975002568745819283535189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29983335045830546189023459 44975002568745819283535189)
          ·
            refine ⟨16470337854765314679029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 44975002568745819283535189 16470337854765314679029)
            ·
              rfl

theorem cell23_7794436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 13].length) (baseStart_7794436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794436 prefixEnd_7794436 := by exact prefixLift 7794436
  have htrace : WordTrace (prefixWord ++ tailWord_7794436) baseStart_7794436 baseEnd_7794436 := by
    simpa [prefixWord, tailWord_7794436, baseEnd_7794436] using wordTrace_append hprefix tailTrace_7794436
  have hstable : (prefixWord ++ tailWord_7794436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794436).length < 2 ^ (prefixWord ++ tailWord_7794436).sum := by decide
  have hdescent : baseEnd_7794436 < baseStart_7794436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794440 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 2, 4]
def baseStart_7794440 : Nat := 118140960795 + 7794440 * 2 ^ 59
def prefixEnd_7794440 : Nat := 4983230072969 + 3 ^ 40 * 7794440 * 2
def baseEnd_7794440 : Nat := 1334098050876863150451343

theorem tailTrace_7794440 : CollatzResearch.WordTrace tailWord_7794440 prefixEnd_7794440 1334098050876863150451343 := by
  unfold tailWord_7794440
  simp only [CollatzResearch.WordTrace]
  refine ⟨142143290941041269608054387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189524387921388359477405849 142143290941041269608054387)
  ·
    refine ⟨213214936411561904412081581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142143290941041269608054387 213214936411561904412081581)
    ·
      refine ⟨79955601154335714154530593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213214936411561904412081581 79955601154335714154530593)
      ·
        refine ⟨59966700865751785615897945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79955601154335714154530593 59966700865751785615897945)
        ·
          refine ⟨44975025649313839211923459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59966700865751785615897945 44975025649313839211923459)
          ·
            refine ⟨67462538473970758817885189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44975025649313839211923459 67462538473970758817885189)
            ·
              refine ⟨12649225963869517278353473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67462538473970758817885189 12649225963869517278353473)
              ·
                refine ⟨9486919472902137958765105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12649225963869517278353473 9486919472902137958765105)
                ·
                  refine ⟨7115189604676603469073829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9486919472902137958765105 7115189604676603469073829)
                  ·
                    refine ⟨1334098050876863150451343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7115189604676603469073829 1334098050876863150451343)
                    ·
                      rfl

theorem cell23_7794440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_7794440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794440 prefixEnd_7794440 := by exact prefixLift 7794440
  have htrace : WordTrace (prefixWord ++ tailWord_7794440) baseStart_7794440 baseEnd_7794440 := by
    simpa [prefixWord, tailWord_7794440, baseEnd_7794440] using wordTrace_append hprefix tailTrace_7794440
  have hstable : (prefixWord ++ tailWord_7794440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794440).length < 2 ^ (prefixWord ++ tailWord_7794440).sum := by decide
  have hdescent : baseEnd_7794440 < baseStart_7794440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794453 : List Nat := [1, 3, 2, 1, 2, 5, 1, 8]
def baseStart_7794453 : Nat := 118140960795 + 7794453 * 2 ^ 59
def prefixEnd_7794453 : Nat := 4983230072969 + 3 ^ 40 * 7794453 * 2
def baseEnd_7794453 : Nat := 148233363995522144462647

theorem tailTrace_7794453 : CollatzResearch.WordTrace tailWord_7794453 prefixEnd_7794453 148233363995522144462647 := by
  unfold tailWord_7794453
  simp only [CollatzResearch.WordTrace]
  refine ⟨284287056031035442436332013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189524704020690294957554675 284287056031035442436332013)
  ·
    refine ⟨106607646011638290913624505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284287056031035442436332013 106607646011638290913624505)
    ·
      refine ⟨79955734508728718185218379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106607646011638290913624505 79955734508728718185218379)
      ·
        refine ⟨119933601763093077277827569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79955734508728718185218379 119933601763093077277827569)
        ·
          refine ⟨89950201322319807958370677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119933601763093077277827569 89950201322319807958370677)
          ·
            refine ⟨8432831373967481996097251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89950201322319807958370677 8432831373967481996097251)
            ·
              refine ⟨12649247060951222994145877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8432831373967481996097251 12649247060951222994145877)
              ·
                refine ⟨148233363995522144462647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12649247060951222994145877 148233363995522144462647)
                ·
                  rfl

theorem cell23_7794453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 8].length) (baseStart_7794453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794453 prefixEnd_7794453 := by exact prefixLift 7794453
  have htrace : WordTrace (prefixWord ++ tailWord_7794453) baseStart_7794453 baseEnd_7794453 := by
    simpa [prefixWord, tailWord_7794453, baseEnd_7794453] using wordTrace_append hprefix tailTrace_7794453
  have hstable : (prefixWord ++ tailWord_7794453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794453).length < 2 ^ (prefixWord ++ tailWord_7794453).sum := by decide
  have hdescent : baseEnd_7794453 < baseStart_7794453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794456 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7794456 : Nat := 118140960795 + 7794456 * 2 ^ 59
def prefixEnd_7794456 : Nat := 4983230072969 + 3 ^ 40 * 7794456 * 2
def baseEnd_7794456 : Nat := 4002302368321061388753955

theorem tailTrace_7794456 : CollatzResearch.WordTrace tailWord_7794456 prefixEnd_7794456 4002302368321061388753955 := by
  unfold tailWord_7794456
  simp only [CollatzResearch.WordTrace]
  refine ⟨142143582725012286974345611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189524776966683049299127481 142143582725012286974345611)
  ·
    refine ⟨213215374087518430461518417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142143582725012286974345611 213215374087518430461518417)
    ·
      refine ⟨159911530565638822846138813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213215374087518430461518417 159911530565638822846138813)
      ·
        refine ⟨59966823962114558567302055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159911530565638822846138813 59966823962114558567302055)
        ·
          refine ⟨89950235943171837850953083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59966823962114558567302055 89950235943171837850953083)
          ·
            refine ⟨134925353914757756776429625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89950235943171837850953083 134925353914757756776429625)
            ·
              refine ⟨101194015436068317582322219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134925353914757756776429625 101194015436068317582322219)
              ·
                refine ⟨151791023154102476373483329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101194015436068317582322219 151791023154102476373483329)
                ·
                  refine ⟨113843267365576857280112497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151791023154102476373483329 113843267365576857280112497)
                  ·
                    refine ⟨85382450524182642960084373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113843267365576857280112497 85382450524182642960084373)
                    ·
                      refine ⟨4002302368321061388753955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85382450524182642960084373 4002302368321061388753955)
                      ·
                        rfl

theorem cell23_7794456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7794456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794456 prefixEnd_7794456 := by exact prefixLift 7794456
  have htrace : WordTrace (prefixWord ++ tailWord_7794456) baseStart_7794456 baseEnd_7794456 := by
    simpa [prefixWord, tailWord_7794456, baseEnd_7794456] using wordTrace_append hprefix tailTrace_7794456
  have hstable : (prefixWord ++ tailWord_7794456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794456).length < 2 ^ (prefixWord ++ tailWord_7794456).sum := by decide
  have hdescent : baseEnd_7794456 < baseStart_7794456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794484 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_7794484 : Nat := 118140960795 + 7794484 * 2 ^ 59
def prefixEnd_7794484 : Nat := 4983230072969 + 3 ^ 40 * 7794484 * 2
def baseEnd_7794484 : Nat := 4002316745779387279203827

theorem tailTrace_7794484 : CollatzResearch.WordTrace tailWord_7794484 prefixEnd_7794484 4002316745779387279203827 := by
  unfold tailWord_7794484
  simp only [CollatzResearch.WordTrace]
  refine ⟨142144093346961567365355253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189525457795948756487140337 142144093346961567365355253)
  ·
    refine ⟨13326008751277646940502055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142144093346961567365355253 13326008751277646940502055)
    ·
      refine ⟨19989013126916470410753083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13326008751277646940502055 19989013126916470410753083)
      ·
        refine ⟨29983519690374705616129625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19989013126916470410753083 29983519690374705616129625)
        ·
          refine ⟨22487639767781029212097219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29983519690374705616129625 22487639767781029212097219)
          ·
            refine ⟨33731459651671543818145829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22487639767781029212097219 33731459651671543818145829)
            ·
              refine ⟨6324648684688414465902343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33731459651671543818145829 6324648684688414465902343)
              ·
                refine ⟨9486973027032621698853515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324648684688414465902343 9486973027032621698853515)
                ·
                  refine ⟨14230459540548932548280273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9486973027032621698853515 14230459540548932548280273)
                  ·
                    refine ⟨10672844655411699411210205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14230459540548932548280273 10672844655411699411210205)
                    ·
                      refine ⟨4002316745779387279203827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10672844655411699411210205 4002316745779387279203827)
                      ·
                        rfl

theorem cell23_7794484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_7794484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794484 prefixEnd_7794484 := by exact prefixLift 7794484
  have htrace : WordTrace (prefixWord ++ tailWord_7794484) baseStart_7794484 baseEnd_7794484 := by
    simpa [prefixWord, tailWord_7794484, baseEnd_7794484] using wordTrace_append hprefix tailTrace_7794484
  have hstable : (prefixWord ++ tailWord_7794484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794484).length < 2 ^ (prefixWord ++ tailWord_7794484).sum := by decide
  have hdescent : baseEnd_7794484 < baseStart_7794484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794513 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 2, 6]
def baseStart_7794513 : Nat := 118140960795 + 7794513 * 2 ^ 59
def prefixEnd_7794513 : Nat := 4983230072969 + 3 ^ 40 * 7794513 * 2
def baseEnd_7794513 : Nat := 1334110545572789221913731

theorem tailTrace_7794513 : CollatzResearch.WordTrace tailWord_7794513 prefixEnd_7794513 1334110545572789221913731 := by
  unfold tailWord_7794513
  simp only [CollatzResearch.WordTrace]
  refine ⟨284289244410818072683516193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189526162940545381789010795 284289244410818072683516193)
  ·
    refine ⟨213216933308113554512637145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284289244410818072683516193 213216933308113554512637145)
    ·
      refine ⟨159912699981085165884477859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213216933308113554512637145 159912699981085165884477859)
      ·
        refine ⟨239869049971627748826716789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159912699981085165884477859 239869049971627748826716789)
        ·
          refine ⟨22487723434840101452504699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239869049971627748826716789 22487723434840101452504699)
          ·
            refine ⟨33731585152260152178757049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22487723434840101452504699 33731585152260152178757049)
            ·
              refine ⟨25298688864195114134067787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33731585152260152178757049 25298688864195114134067787)
              ·
                refine ⟨37948033296292671201101681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25298688864195114134067787 37948033296292671201101681)
                ·
                  refine ⟨28461024972219503400826261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37948033296292671201101681 28461024972219503400826261)
                  ·
                    refine ⟨1334110545572789221913731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28461024972219503400826261 1334110545572789221913731)
                    ·
                      rfl

theorem cell23_7794513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_7794513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794513 prefixEnd_7794513 := by exact prefixLift 7794513
  have htrace : WordTrace (prefixWord ++ tailWord_7794513) baseStart_7794513 baseEnd_7794513 := by
    simpa [prefixWord, tailWord_7794513, baseEnd_7794513] using wordTrace_append hprefix tailTrace_7794513
  have hstable : (prefixWord ++ tailWord_7794513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794513).length < 2 ^ (prefixWord ++ tailWord_7794513).sum := by decide
  have hdescent : baseEnd_7794513 < baseStart_7794513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794514 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_7794514 : Nat := 118140960795 + 7794514 * 2 ^ 59
def prefixEnd_7794514 : Nat := 4983230072969 + 3 ^ 40 * 7794514 * 2
def baseEnd_7794514 : Nat := 4002332150199022161828689

theorem tailTrace_7794514 : CollatzResearch.WordTrace tailWord_7794514 prefixEnd_7794514 4002332150199022161828689 := by
  unfold tailWord_7794514
  simp only [CollatzResearch.WordTrace]
  refine ⟨71072320220953612463575649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189526187255876299902868397 71072320220953612463575649)
  ·
    refine ⟨53304240165715209347681737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71072320220953612463575649 53304240165715209347681737)
    ·
      refine ⟨39978180124286407010761303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53304240165715209347681737 39978180124286407010761303)
      ·
        refine ⟨59967270186429610516141955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39978180124286407010761303 59967270186429610516141955)
        ·
          refine ⟨89950905279644415774212933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59967270186429610516141955 89950905279644415774212933)
          ·
            refine ⟨16865794739933327957664925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89950905279644415774212933 16865794739933327957664925)
            ·
              refine ⟨6324673027474997984124347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16865794739933327957664925 6324673027474997984124347)
              ·
                refine ⟨9487009541212496976186521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324673027474997984124347 9487009541212496976186521)
                ·
                  refine ⟨7115257155909372732139891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9487009541212496976186521 7115257155909372732139891)
                  ·
                    refine ⟨10672885733864059098209837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7115257155909372732139891 10672885733864059098209837)
                    ·
                      refine ⟨4002332150199022161828689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10672885733864059098209837 4002332150199022161828689)
                      ·
                        rfl

theorem cell23_7794514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_7794514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794514 prefixEnd_7794514 := by exact prefixLift 7794514
  have htrace : WordTrace (prefixWord ++ tailWord_7794514) baseStart_7794514 baseEnd_7794514 := by
    simpa [prefixWord, tailWord_7794514, baseEnd_7794514] using wordTrace_append hprefix tailTrace_7794514
  have hstable : (prefixWord ++ tailWord_7794514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794514).length < 2 ^ (prefixWord ++ tailWord_7794514).sum := by decide
  have hdescent : baseEnd_7794514 < baseStart_7794514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794610 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_7794610 : Nat := 118140960795 + 7794610 * 2 ^ 59
def prefixEnd_7794610 : Nat := 4983230072969 + 3 ^ 40 * 7794610 * 2
def baseEnd_7794610 : Nat := 4002381444341853786228247

theorem tailTrace_7794610 : CollatzResearch.WordTrace tailWord_7794610 prefixEnd_7794610 4002381444341853786228247 := by
  unfold tailWord_7794610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71073195572866664562449321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189528521527644438833198189 71073195572866664562449321)
  ·
    refine ⟨53304896679649998421836991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71073195572866664562449321 53304896679649998421836991)
    ·
      refine ⟨79957345019474997632755487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53304896679649998421836991 79957345019474997632755487)
      ·
        refine ⟨119936017529212496449133231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79957345019474997632755487 119936017529212496449133231)
        ·
          refine ⟨179904026293818744673699847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119936017529212496449133231 179904026293818744673699847)
          ·
            refine ⟨269856039440728117010549771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179904026293818744673699847 269856039440728117010549771)
            ·
              refine ⟨404784059161092175515824657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269856039440728117010549771 404784059161092175515824657)
              ·
                refine ⟨303588044370819131636868493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404784059161092175515824657 303588044370819131636868493)
                ·
                  refine ⟨113845516639057174363825685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303588044370819131636868493 113845516639057174363825685)
                  ·
                    refine ⟨5336508592455805048304329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113845516639057174363825685 5336508592455805048304329)
                    ·
                      refine ⟨4002381444341853786228247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336508592455805048304329 4002381444341853786228247)
                      ·
                        rfl

theorem cell23_7794610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_7794610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794610 prefixEnd_7794610 := by exact prefixLift 7794610
  have htrace : WordTrace (prefixWord ++ tailWord_7794610) baseStart_7794610 baseEnd_7794610 := by
    simpa [prefixWord, tailWord_7794610, baseEnd_7794610] using wordTrace_append hprefix tailTrace_7794610
  have hstable : (prefixWord ++ tailWord_7794610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794610).length < 2 ^ (prefixWord ++ tailWord_7794610).sum := by decide
  have hdescent : baseEnd_7794610 < baseStart_7794610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794670 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_7794670 : Nat := 118140960795 + 7794670 * 2 ^ 59
def prefixEnd_7794670 : Nat := 4983230072969 + 3 ^ 40 * 7794670 * 2
def baseEnd_7794670 : Nat := 4002412253181123551477971

theorem tailTrace_7794670 : CollatzResearch.WordTrace tailWord_7794670 prefixEnd_7794670 4002412253181123551477971 := by
  unfold tailWord_7794670
  simp only [CollatzResearch.WordTrace]
  refine ⟨35536871333906161062122683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189529980447499525664654309 35536871333906161062122683)
  ·
    refine ⟨53305307000859241593184025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35536871333906161062122683 53305307000859241593184025)
    ·
      refine ⟨39978980250644431194888019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53305307000859241593184025 39978980250644431194888019)
      ·
        refine ⟨59968470375966646792332029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39978980250644431194888019 59968470375966646792332029)
        ·
          refine ⟨22488176390987492547124511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59968470375966646792332029 22488176390987492547124511)
          ·
            refine ⟨33732264586481238820686767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22488176390987492547124511 33732264586481238820686767)
            ·
              refine ⟨50598396879721858231030151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33732264586481238820686767 50598396879721858231030151)
              ·
                refine ⟨75897595319582787346545227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50598396879721858231030151 75897595319582787346545227)
                ·
                  refine ⟨113846392979374181019817841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75897595319582787346545227 113846392979374181019817841)
                  ·
                    refine ⟨85384794734530635764863381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113846392979374181019817841 85384794734530635764863381)
                    ·
                      refine ⟨4002412253181123551477971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85384794734530635764863381 4002412253181123551477971)
                      ·
                        rfl

theorem cell23_7794670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_7794670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794670 prefixEnd_7794670 := by exact prefixLift 7794670
  have htrace : WordTrace (prefixWord ++ tailWord_7794670) baseStart_7794670 baseEnd_7794670 := by
    simpa [prefixWord, tailWord_7794670, baseEnd_7794670] using wordTrace_append hprefix tailTrace_7794670
  have hstable : (prefixWord ++ tailWord_7794670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794670).length < 2 ^ (prefixWord ++ tailWord_7794670).sum := by decide
  have hdescent : baseEnd_7794670 < baseStart_7794670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794703 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_7794703 : Nat := 118140960795 + 7794703 * 2 ^ 59
def prefixEnd_7794703 : Nat := 4983230072969 + 3 ^ 40 * 7794703 * 2
def baseEnd_7794703 : Nat := 4002429198042721922365319

theorem tailTrace_7794703 : CollatzResearch.WordTrace tailWord_7794703 prefixEnd_7794703 4002429198042721922365319 := by
  unfold tailWord_7794703
  simp only [CollatzResearch.WordTrace]
  refine ⟨284296174280129735132932763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189530782853419823421955175 284296174280129735132932763)
  ·
    refine ⟨426444261420194602699399145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284296174280129735132932763 426444261420194602699399145)
    ·
      refine ⟨319833196065145952024549359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426444261420194602699399145 319833196065145952024549359)
      ·
        refine ⟨479749794097718928036824039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319833196065145952024549359 479749794097718928036824039)
        ·
          refine ⟨719624691146578392055236059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479749794097718928036824039 719624691146578392055236059)
          ·
            refine ⟨1079437036719867588082854089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719624691146578392055236059 1079437036719867588082854089)
            ·
              refine ⟨809577777539900691062140567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079437036719867588082854089 809577777539900691062140567)
              ·
                refine ⟨1214366666309851036593210851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809577777539900691062140567 1214366666309851036593210851)
                ·
                  refine ⟨1821549999464776554889816277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214366666309851036593210851 1821549999464776554889816277)
                  ·
                    refine ⟨42692578112455700505230069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1821549999464776554889816277 42692578112455700505230069)
                    ·
                      refine ⟨4002429198042721922365319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42692578112455700505230069 4002429198042721922365319)
                      ·
                        rfl

theorem cell23_7794703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_7794703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794703 prefixEnd_7794703 := by exact prefixLift 7794703
  have htrace : WordTrace (prefixWord ++ tailWord_7794703) baseStart_7794703 baseEnd_7794703 := by
    simpa [prefixWord, tailWord_7794703, baseEnd_7794703] using wordTrace_append hprefix tailTrace_7794703
  have hstable : (prefixWord ++ tailWord_7794703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794703).length < 2 ^ (prefixWord ++ tailWord_7794703).sum := by decide
  have hdescent : baseEnd_7794703 < baseStart_7794703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794728 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7794728 : Nat := 118140960795 + 7794728 * 2 ^ 59
def prefixEnd_7794728 : Nat := 4983230072969 + 3 ^ 40 * 7794728 * 2
def baseEnd_7794728 : Nat := 4002442035059084324552705

theorem tailTrace_7794728 : CollatzResearch.WordTrace tailWord_7794728 prefixEnd_7794728 4002442035059084324552705 := by
  unfold tailWord_7794728
  simp only [CollatzResearch.WordTrace]
  refine ⟨142148543052519582201296419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189531390736692776268395225 142148543052519582201296419)
  ·
    refine ⟨213222814578779373301944629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142148543052519582201296419 213222814578779373301944629)
    ·
      refine ⟨19989638866760566247057309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213222814578779373301944629 19989638866760566247057309)
      ·
        refine ⟨7496114575035212342646491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19989638866760566247057309 7496114575035212342646491)
        ·
          refine ⟨11244171862552818513969737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7496114575035212342646491 11244171862552818513969737)
          ·
            refine ⟨8433128896914613885477303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11244171862552818513969737 8433128896914613885477303)
            ·
              refine ⟨12649693345371920828215955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433128896914613885477303 12649693345371920828215955)
              ·
                refine ⟨18974540018057881242323933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12649693345371920828215955 18974540018057881242323933)
                ·
                  refine ⟨7115452506771705465871475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18974540018057881242323933 7115452506771705465871475)
                  ·
                    refine ⟨10673178760157558198807213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7115452506771705465871475 10673178760157558198807213)
                    ·
                      refine ⟨4002442035059084324552705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10673178760157558198807213 4002442035059084324552705)
                      ·
                        rfl

theorem cell23_7794728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7794728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794728 prefixEnd_7794728 := by exact prefixLift 7794728
  have htrace : WordTrace (prefixWord ++ tailWord_7794728) baseStart_7794728 baseEnd_7794728 := by
    simpa [prefixWord, tailWord_7794728, baseEnd_7794728] using wordTrace_append hprefix tailTrace_7794728
  have hstable : (prefixWord ++ tailWord_7794728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794728).length < 2 ^ (prefixWord ++ tailWord_7794728).sum := by decide
  have hdescent : baseEnd_7794728 < baseStart_7794728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794744 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 2, 4]
def baseStart_7794744 : Nat := 118140960795 + 7794744 * 2 ^ 59
def prefixEnd_7794744 : Nat := 4983230072969 + 3 ^ 40 * 7794744 * 2
def baseEnd_7794744 : Nat := 1334150083583185420650877

theorem tailTrace_7794744 : CollatzResearch.WordTrace tailWord_7794744 prefixEnd_7794744 1334150083583185420650877 := by
  unfold tailWord_7794744
  simp only [CollatzResearch.WordTrace]
  refine ⟨142148834836490599567587643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189531779781987466090116857 142148834836490599567587643)
  ·
    refine ⟨213223252254735899351381465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142148834836490599567587643 213223252254735899351381465)
    ·
      refine ⟨159917439191051924513536099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213223252254735899351381465 159917439191051924513536099)
      ·
        refine ⟨239876158786577886770304149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159917439191051924513536099 239876158786577886770304149)
        ·
          refine ⟨11244194943120838442358007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239876158786577886770304149 11244194943120838442358007)
          ·
            refine ⟨16866292414681257663537011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11244194943120838442358007 16866292414681257663537011)
            ·
              refine ⟨25299438622021886495305517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16866292414681257663537011 25299438622021886495305517)
              ·
                refine ⟨9487289483258207435739569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25299438622021886495305517 9487289483258207435739569)
                ·
                  refine ⟨7115467112443655576804677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9487289483258207435739569 7115467112443655576804677)
                  ·
                    refine ⟨1334150083583185420650877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7115467112443655576804677 1334150083583185420650877)
                    ·
                      rfl

theorem cell23_7794744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_7794744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794744 prefixEnd_7794744 := by exact prefixLift 7794744
  have htrace : WordTrace (prefixWord ++ tailWord_7794744) baseStart_7794744 baseEnd_7794744 := by
    simpa [prefixWord, tailWord_7794744, baseEnd_7794744] using wordTrace_append hprefix tailTrace_7794744
  have hstable : (prefixWord ++ tailWord_7794744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794744).length < 2 ^ (prefixWord ++ tailWord_7794744).sum := by decide
  have hdescent : baseEnd_7794744 < baseStart_7794744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794784 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 2, 1, 3]
def baseStart_7794784 : Nat := 118140960795 + 7794784 * 2 ^ 59
def prefixEnd_7794784 : Nat := 4983230072969 + 3 ^ 40 * 7794784 * 2
def baseEnd_7794784 : Nat := 4002470789975736105452447

theorem tailTrace_7794784 : CollatzResearch.WordTrace tailWord_7794784 prefixEnd_7794784 4002470789975736105452447 := by
  unfold tailWord_7794784
  simp only [CollatzResearch.WordTrace]
  refine ⟨142149564296418142983315703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189532752395224190644420937 142149564296418142983315703)
  ·
    refine ⟨213224346444627214474973555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142149564296418142983315703 213224346444627214474973555)
    ·
      refine ⟨319836519666940821712460333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213224346444627214474973555 319836519666940821712460333)
      ·
        refine ⟨119938694875102808142172625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319836519666940821712460333 119938694875102808142172625)
        ·
          refine ⟨89954021156327106106629469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119938694875102808142172625 89954021156327106106629469)
          ·
            refine ⟨33732757933622664789986051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89954021156327106106629469 33732757933622664789986051)
            ·
              refine ⟨50599136900433997184979077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33732757933622664789986051 50599136900433997184979077)
              ·
                refine ⟨9487338168831374472183577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50599136900433997184979077 9487338168831374472183577)
                ·
                  refine ⟨7115503626623530854137683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9487338168831374472183577 7115503626623530854137683)
                  ·
                    refine ⟨10673255439935296281206525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7115503626623530854137683 10673255439935296281206525)
                    ·
                      refine ⟨4002470789975736105452447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10673255439935296281206525 4002470789975736105452447)
                      ·
                        rfl

theorem cell23_7794784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_7794784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794784 prefixEnd_7794784 := by exact prefixLift 7794784
  have htrace : WordTrace (prefixWord ++ tailWord_7794784) baseStart_7794784 baseEnd_7794784 := by
    simpa [prefixWord, tailWord_7794784, baseEnd_7794784] using wordTrace_append hprefix tailTrace_7794784
  have hstable : (prefixWord ++ tailWord_7794784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794784).length < 2 ^ (prefixWord ++ tailWord_7794784).sum := by decide
  have hdescent : baseEnd_7794784 < baseStart_7794784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794800 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 1, 8]
def baseStart_7794800 : Nat := 118140960795 + 7794800 * 2 ^ 59
def prefixEnd_7794800 : Nat := 4983230072969 + 3 ^ 40 * 7794800 * 2
def baseEnd_7794800 : Nat := 1334159668555402680950791

theorem tailTrace_7794800 : CollatzResearch.WordTrace tailWord_7794800 prefixEnd_7794800 1334159668555402680950791 := by
  unfold tailWord_7794800
  simp only [CollatzResearch.WordTrace]
  refine ⟨142149856080389160349606927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189533141440518880466142569 142149856080389160349606927)
  ·
    refine ⟨213224784120583740524410391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142149856080389160349606927 213224784120583740524410391)
    ·
      refine ⟨319837176180875610786615587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213224784120583740524410391 319837176180875610786615587)
      ·
        refine ⟨479755764271313416179923381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319837176180875610786615587 479755764271313416179923381)
        ·
          refine ⟨44977102900435632766867817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479755764271313416179923381 44977102900435632766867817)
          ·
            refine ⟨33732827175326724575150863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44977102900435632766867817 33732827175326724575150863)
            ·
              refine ⟨50599240762990086862726295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33732827175326724575150863 50599240762990086862726295)
              ·
                refine ⟨75898861144485130294089443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50599240762990086862726295 75898861144485130294089443)
                ·
                  refine ⟨113848291716727695441134165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75898861144485130294089443 113848291716727695441134165)
                  ·
                    refine ⟨1334159668555402680950791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113848291716727695441134165 1334159668555402680950791)
                    ·
                      rfl

theorem cell23_7794800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_7794800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794800 prefixEnd_7794800 := by exact prefixLift 7794800
  have htrace : WordTrace (prefixWord ++ tailWord_7794800) baseStart_7794800 baseEnd_7794800 := by
    simpa [prefixWord, tailWord_7794800, baseEnd_7794800] using wordTrace_append hprefix tailTrace_7794800
  have hstable : (prefixWord ++ tailWord_7794800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794800).length < 2 ^ (prefixWord ++ tailWord_7794800).sum := by decide
  have hdescent : baseEnd_7794800 < baseStart_7794800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794847 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 7]
def baseStart_7794847 : Nat := 118140960795 + 7794847 * 2 ^ 59
def prefixEnd_7794847 : Nat := 4983230072969 + 3 ^ 40 * 7794847 * 2
def baseEnd_7794847 : Nat := 444722571028552150996073

theorem tailTrace_7794847 : CollatzResearch.WordTrace tailWord_7794847 prefixEnd_7794847 444722571028552150996073 := by
  unfold tailWord_7794847
  simp only [CollatzResearch.WordTrace]
  refine ⟨284301426391608047726174795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189534284261072031817449863 284301426391608047726174795)
  ·
    refine ⟨426452139587412071589262193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284301426391608047726174795 426452139587412071589262193)
    ·
      refine ⟨319839104690559053691946645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426452139587412071589262193 319839104690559053691946645)
      ·
        refine ⟨14992458032369955641809999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 319839104690559053691946645 14992458032369955641809999)
        ·
          refine ⟨22488687048554933462714999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14992458032369955641809999 22488687048554933462714999)
          ·
            refine ⟨33733030572832400194072499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22488687048554933462714999 33733030572832400194072499)
            ·
              refine ⟨50599545859248600291108749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33733030572832400194072499 50599545859248600291108749)
              ·
                refine ⟨18974829697218225109165781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50599545859248600291108749 18974829697218225109165781)
                ·
                  refine ⟨444722571028552150996073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18974829697218225109165781 444722571028552150996073)
                  ·
                    rfl

theorem cell23_7794847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 7].length) (baseStart_7794847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794847 prefixEnd_7794847 := by exact prefixLift 7794847
  have htrace : WordTrace (prefixWord ++ tailWord_7794847) baseStart_7794847 baseEnd_7794847 := by
    simpa [prefixWord, tailWord_7794847, baseEnd_7794847] using wordTrace_append hprefix tailTrace_7794847
  have hstable : (prefixWord ++ tailWord_7794847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794847).length < 2 ^ (prefixWord ++ tailWord_7794847).sum := by decide
  have hdescent : baseEnd_7794847 < baseStart_7794847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794877 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_7794877 : Nat := 118140960795 + 7794877 * 2 ^ 59
def prefixEnd_7794877 : Nat := 4983230072969 + 3 ^ 40 * 7794877 * 2
def baseEnd_7794877 : Nat := 1334172847892201413863173

theorem tailTrace_7794877 : CollatzResearch.WordTrace tailWord_7794877 prefixEnd_7794877 1334172847892201413863173 := by
  unfold tailWord_7794877
  simp only [CollatzResearch.WordTrace]
  refine ⟨284302520581499362849766885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189535013720999575233177923 284302520581499362849766885)
  ·
    refine ⟨53306722609031130534331291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284302520581499362849766885 53306722609031130534331291)
    ·
      refine ⟨79960083913546695801496937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53306722609031130534331291 79960083913546695801496937)
      ·
        refine ⟨59970062935160021851122703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79960083913546695801496937 59970062935160021851122703)
        ·
          refine ⟨89955094402740032776684055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59970062935160021851122703 89955094402740032776684055)
          ·
            refine ⟨134932641604110049165026083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89955094402740032776684055 134932641604110049165026083)
            ·
              refine ⟨202398962406165073747539125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134932641604110049165026083 202398962406165073747539125)
              ·
                refine ⟨18974902725577975663831793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202398962406165073747539125 18974902725577975663831793)
                ·
                  refine ⟨14231177044183481747873845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18974902725577975663831793 14231177044183481747873845)
                  ·
                    refine ⟨1334172847892201413863173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14231177044183481747873845 1334172847892201413863173)
                    ·
                      rfl

theorem cell23_7794877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_7794877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794877 prefixEnd_7794877 := by exact prefixLift 7794877
  have htrace : WordTrace (prefixWord ++ tailWord_7794877) baseStart_7794877 baseEnd_7794877 := by
    simpa [prefixWord, tailWord_7794877, baseEnd_7794877] using wordTrace_append hprefix tailTrace_7794877
  have hstable : (prefixWord ++ tailWord_7794877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794877).length < 2 ^ (prefixWord ++ tailWord_7794877).sum := by decide
  have hdescent : baseEnd_7794877 < baseStart_7794877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794894 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_7794894 : Nat := 118140960795 + 7794894 * 2 ^ 59
def prefixEnd_7794894 : Nat := 4983230072969 + 3 ^ 40 * 7794894 * 2
def baseEnd_7794894 : Nat := 1334175757615910225025647

theorem tailTrace_7794894 : CollatzResearch.WordTrace tailWord_7794894 prefixEnd_7794894 1334175757615910225025647 := by
  unfold tailWord_7794894
  simp only [CollatzResearch.WordTrace]
  refine ⟨35537892577804721844141967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189535427081625183168757157 35537892577804721844141967)
  ·
    refine ⟨53306838866707082766212951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35537892577804721844141967 53306838866707082766212951)
    ·
      refine ⟨79960258300060624149319427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53306838866707082766212951 79960258300060624149319427)
      ·
        refine ⟨119940387450090936223979141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79960258300060624149319427 119940387450090936223979141)
        ·
          refine ⟨22488822646892050541996089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119940387450090936223979141 22488822646892050541996089)
          ·
            refine ⟨16866616985169037906497067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22488822646892050541996089 16866616985169037906497067)
            ·
              refine ⟨25299925477753556859745601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16866616985169037906497067 25299925477753556859745601)
              ·
                refine ⟨18974944108315167644809201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25299925477753556859745601 18974944108315167644809201)
                ·
                  refine ⟨14231208081236375733606901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18974944108315167644809201 14231208081236375733606901)
                  ·
                    refine ⟨1334175757615910225025647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14231208081236375733606901 1334175757615910225025647)
                    ·
                      rfl

theorem cell23_7794894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_7794894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794894 prefixEnd_7794894 := by exact prefixLift 7794894
  have htrace : WordTrace (prefixWord ++ tailWord_7794894) baseStart_7794894 baseEnd_7794894 := by
    simpa [prefixWord, tailWord_7794894, baseEnd_7794894] using wordTrace_append hprefix tailTrace_7794894
  have hstable : (prefixWord ++ tailWord_7794894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794894).length < 2 ^ (prefixWord ++ tailWord_7794894).sum := by decide
  have hdescent : baseEnd_7794894 < baseStart_7794894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794897 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_7794897 : Nat := 118140960795 + 7794897 * 2 ^ 59
def prefixEnd_7794897 : Nat := 4983230072969 + 3 ^ 40 * 7794897 * 2
def baseEnd_7794897 : Nat := 4002528813289694163339427

theorem tailTrace_7794897 : CollatzResearch.WordTrace tailWord_7794897 prefixEnd_7794897 4002528813289694163339427 := by
  unfold tailWord_7794897
  simp only [CollatzResearch.WordTrace]
  refine ⟨284303250041426906265494945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189535500027617937510329963 284303250041426906265494945)
  ·
    refine ⟨213227437531070179699121209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284303250041426906265494945 213227437531070179699121209)
    ·
      refine ⟨159920578148302634774340907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213227437531070179699121209 159920578148302634774340907)
      ·
        refine ⟨239880867222453952161511361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159920578148302634774340907 239880867222453952161511361)
        ·
          refine ⟨179910650416840464121133521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239880867222453952161511361 179910650416840464121133521)
          ·
            refine ⟨134932987812630348090850141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179910650416840464121133521 134932987812630348090850141)
            ·
              refine ⟨50599870429736380534068803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134932987812630348090850141 50599870429736380534068803)
              ·
                refine ⟨75899805644604570801103205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50599870429736380534068803 75899805644604570801103205)
                ·
                  refine ⟨14231213558363357025206851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75899805644604570801103205 14231213558363357025206851)
                  ·
                    refine ⟨21346820337545035537810277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14231213558363357025206851 21346820337545035537810277)
                    ·
                      refine ⟨4002528813289694163339427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21346820337545035537810277 4002528813289694163339427)
                      ·
                        rfl

theorem cell23_7794897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_7794897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794897 prefixEnd_7794897 := by exact prefixLift 7794897
  have htrace : WordTrace (prefixWord ++ tailWord_7794897) baseStart_7794897 baseEnd_7794897 := by
    simpa [prefixWord, tailWord_7794897, baseEnd_7794897] using wordTrace_append hprefix tailTrace_7794897
  have hstable : (prefixWord ++ tailWord_7794897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794897).length < 2 ^ (prefixWord ++ tailWord_7794897).sum := by decide
  have hdescent : baseEnd_7794897 < baseStart_7794897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794934 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_7794934 : Nat := 118140960795 + 7794934 * 2 ^ 59
def prefixEnd_7794934 : Nat := 4983230072969 + 3 ^ 40 * 7794934 * 2
def baseEnd_7794934 : Nat := 4002547812073910518576757

theorem tailTrace_7794934 : CollatzResearch.WordTrace tailWord_7794934 prefixEnd_7794934 4002547812073910518576757 := by
  unfold tailWord_7794934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17769037471393303849036991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189536399694861907723061237 17769037471393303849036991)
  ·
    refine ⟨26653556207089955773555487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17769037471393303849036991 26653556207089955773555487)
    ·
      refine ⟨39980334310634933660333231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26653556207089955773555487 39980334310634933660333231)
      ·
        refine ⟨59970501465952400490499847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39980334310634933660333231 59970501465952400490499847)
        ·
          refine ⟨89955752198928600735749771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59970501465952400490499847 89955752198928600735749771)
          ·
            refine ⟨134933628298392901103624657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89955752198928600735749771 134933628298392901103624657)
            ·
              refine ⟨101200221223794675827718493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134933628298392901103624657 101200221223794675827718493)
              ·
                refine ⟨37950082958923003435394435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101200221223794675827718493 37950082958923003435394435)
                ·
                  refine ⟨56925124438384505153091653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37950082958923003435394435 56925124438384505153091653)
                  ·
                    refine ⟨10673460832197094716204685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56925124438384505153091653 10673460832197094716204685)
                    ·
                      refine ⟨4002547812073910518576757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10673460832197094716204685 4002547812073910518576757)
                      ·
                        rfl

theorem cell23_7794934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_7794934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794934 prefixEnd_7794934 := by exact prefixLift 7794934
  have htrace : WordTrace (prefixWord ++ tailWord_7794934) baseStart_7794934 baseEnd_7794934 := by
    simpa [prefixWord, tailWord_7794934, baseEnd_7794934] using wordTrace_append hprefix tailTrace_7794934
  have hstable : (prefixWord ++ tailWord_7794934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794934).length < 2 ^ (prefixWord ++ tailWord_7794934).sum := by decide
  have hdescent : baseEnd_7794934 < baseStart_7794934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7794991 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 2, 3, 2]
def baseStart_7794991 : Nat := 118140960795 + 7794991 * 2 ^ 59
def prefixEnd_7794991 : Nat := 4983230072969 + 3 ^ 40 * 7794991 * 2
def baseEnd_7794991 : Nat := 4002577080471216795563995

theorem tailTrace_7794991 : CollatzResearch.WordTrace tailWord_7794991 prefixEnd_7794991 4002577080471216795563995 := by
  unfold tailWord_7794991
  simp only [CollatzResearch.WordTrace]
  refine ⟨284306678503086360319416827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189537785668724240212944551 284306678503086360319416827)
  ·
    refine ⟨426460017754629540479125241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284306678503086360319416827 426460017754629540479125241)
    ·
      refine ⟨319845013315972155359343931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426460017754629540479125241 319845013315972155359343931)
      ·
        refine ⟨479767519973958233039015897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319845013315972155359343931 479767519973958233039015897)
        ·
          refine ⟨359825639980468674779261923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479767519973958233039015897 359825639980468674779261923)
          ·
            refine ⟨539738459970703012168892885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359825639980468674779261923 539738459970703012168892885)
            ·
              refine ⟨12650120155563351847708427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 539738459970703012168892885 12650120155563351847708427)
              ·
                refine ⟨18975180233345027771562641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12650120155563351847708427 18975180233345027771562641)
                ·
                  refine ⟨14231385175008770828671981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18975180233345027771562641 14231385175008770828671981)
                  ·
                    refine ⟨5336769440628289060751993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14231385175008770828671981 5336769440628289060751993)
                    ·
                      refine ⟨4002577080471216795563995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336769440628289060751993 4002577080471216795563995)
                      ·
                        rfl

theorem cell23_7794991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3, 2].length) (baseStart_7794991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7794991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7794991 prefixEnd_7794991 := by exact prefixLift 7794991
  have htrace : WordTrace (prefixWord ++ tailWord_7794991) baseStart_7794991 baseEnd_7794991 := by
    simpa [prefixWord, tailWord_7794991, baseEnd_7794991] using wordTrace_append hprefix tailTrace_7794991
  have hstable : (prefixWord ++ tailWord_7794991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7794991).length < 2 ^ (prefixWord ++ tailWord_7794991).sum := by decide
  have hdescent : baseEnd_7794991 < baseStart_7794991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7794991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795001 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 1, 5]
def baseStart_7795001 : Nat := 118140960795 + 7795001 * 2 ^ 59
def prefixEnd_7795001 : Nat := 4983230072969 + 3 ^ 40 * 7795001 * 2
def baseEnd_7795001 : Nat := 1334194071759253918812983

theorem tailTrace_7795001 : CollatzResearch.WordTrace tailWord_7795001 prefixEnd_7795001 1334194071759253918812983 := by
  unfold tailWord_7795001
  simp only [CollatzResearch.WordTrace]
  refine ⟨284307043233050132027280857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189538028822033421351520571 284307043233050132027280857)
  ·
    refine ⟨213230282424787599020460643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284307043233050132027280857 213230282424787599020460643)
    ·
      refine ⟨319845423637181398530690965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213230282424787599020460643 319845423637181398530690965)
      ·
        refine ⟨14992754232992878056126139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 319845423637181398530690965 14992754232992878056126139)
        ·
          refine ⟨22489131349489317084189209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14992754232992878056126139 22489131349489317084189209)
          ·
            refine ⟨16866848512116987813141907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22489131349489317084189209 16866848512116987813141907)
            ·
              refine ⟨25300272768175481719712861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16866848512116987813141907 25300272768175481719712861)
              ·
                refine ⟨9487602288065805644892323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25300272768175481719712861 9487602288065805644892323)
                ·
                  refine ⟨14231403432098708467338485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9487602288065805644892323 14231403432098708467338485)
                  ·
                    refine ⟨1334194071759253918812983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14231403432098708467338485 1334194071759253918812983)
                    ·
                      rfl

theorem cell23_7795001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_7795001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795001 prefixEnd_7795001 := by exact prefixLift 7795001
  have htrace : WordTrace (prefixWord ++ tailWord_7795001) baseStart_7795001 baseEnd_7795001 := by
    simpa [prefixWord, tailWord_7795001, baseEnd_7795001] using wordTrace_append hprefix tailTrace_7795001
  have hstable : (prefixWord ++ tailWord_7795001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795001).length < 2 ^ (prefixWord ++ tailWord_7795001).sum := by decide
  have hdescent : baseEnd_7795001 < baseStart_7795001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795017 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_7795017 : Nat := 118140960795 + 7795017 * 2 ^ 59
def prefixEnd_7795017 : Nat := 4983230072969 + 3 ^ 40 * 7795017 * 2
def baseEnd_7795017 : Nat := 4002590430968233693838875

theorem tailTrace_7795017 : CollatzResearch.WordTrace tailWord_7795017 prefixEnd_7795017 4002590430968233693838875 := by
  unfold tailWord_7795017
  simp only [CollatzResearch.WordTrace]
  refine ⟨284307626800992166759863305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189538417867328111173242203 284307626800992166759863305)
  ·
    refine ⟨213230720100744125069897479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284307626800992166759863305 213230720100744125069897479)
    ·
      refine ⟨319846080151116187604846219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213230720100744125069897479 319846080151116187604846219)
      ·
        refine ⟨479769120226674281407269329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319846080151116187604846219 479769120226674281407269329)
        ·
          refine ⟨359826840170005711055451997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479769120226674281407269329 359826840170005711055451997)
          ·
            refine ⟨134935065063752141645794499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359826840170005711055451997 134935065063752141645794499)
            ·
              refine ⟨202402597595628212468691749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134935065063752141645794499 202402597595628212468691749)
              ·
                refine ⟨37950487049180289837879703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202402597595628212468691749 37950487049180289837879703)
                ·
                  refine ⟨56925730573770434756819555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37950487049180289837879703 56925730573770434756819555)
                  ·
                    refine ⟨85388595860655652135229333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56925730573770434756819555 85388595860655652135229333)
                    ·
                      refine ⟨4002590430968233693838875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85388595860655652135229333 4002590430968233693838875)
                      ·
                        rfl

theorem cell23_7795017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_7795017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795017 prefixEnd_7795017 := by exact prefixLift 7795017
  have htrace : WordTrace (prefixWord ++ tailWord_7795017) baseStart_7795017 baseEnd_7795017 := by
    simpa [prefixWord, tailWord_7795017, baseEnd_7795017] using wordTrace_append hprefix tailTrace_7795017
  have hstable : (prefixWord ++ tailWord_7795017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795017).length < 2 ^ (prefixWord ++ tailWord_7795017).sum := by decide
  have hdescent : baseEnd_7795017 < baseStart_7795017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795024 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_7795024 : Nat := 118140960795 + 7795024 * 2 ^ 59
def prefixEnd_7795024 : Nat := 4983230072969 + 3 ^ 40 * 7795024 * 2
def baseEnd_7795024 : Nat := 4002594025332815166451343

theorem tailTrace_7795024 : CollatzResearch.WordTrace tailWord_7795024 prefixEnd_7795024 4002594025332815166451343 := by
  unfold tailWord_7795024
  simp only [CollatzResearch.WordTrace]
  refine ⟨142153941055983403477684063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189538588074644537970245417 142153941055983403477684063)
  ·
    refine ⟨213230911583975105216526095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142153941055983403477684063 213230911583975105216526095)
    ·
      refine ⟨319846367375962657824789143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213230911583975105216526095 319846367375962657824789143)
      ·
        refine ⟨479769551063943986737183715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319846367375962657824789143 479769551063943986737183715)
        ·
          refine ⟨719654326595915980105775573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479769551063943986737183715 719654326595915980105775573)
          ·
            refine ⟨16866898279591780783729115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 719654326595915980105775573 16866898279591780783729115)
            ·
              refine ⟨25300347419387671175593673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16866898279591780783729115 25300347419387671175593673)
              ·
                refine ⟨18975260564540753381695255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25300347419387671175593673 18975260564540753381695255)
                ·
                  refine ⟨28462890846811130072542883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18975260564540753381695255 28462890846811130072542883)
                  ·
                    refine ⟨42694336270216695108814325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28462890846811130072542883 42694336270216695108814325)
                    ·
                      refine ⟨4002594025332815166451343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42694336270216695108814325 4002594025332815166451343)
                      ·
                        rfl

theorem cell23_7795024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_7795024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795024 prefixEnd_7795024 := by exact prefixLift 7795024
  have htrace : WordTrace (prefixWord ++ tailWord_7795024) baseStart_7795024 baseEnd_7795024 := by
    simpa [prefixWord, tailWord_7795024, baseEnd_7795024] using wordTrace_append hprefix tailTrace_7795024
  have hstable : (prefixWord ++ tailWord_7795024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795024).length < 2 ^ (prefixWord ++ tailWord_7795024).sum := by decide
  have hdescent : baseEnd_7795024 < baseStart_7795024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795057 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 9]
def baseStart_7795057 : Nat := 118140960795 + 7795057 * 2 ^ 59
def prefixEnd_7795057 : Nat := 4983230072969 + 3 ^ 40 * 7795057 * 2
def baseEnd_7795057 : Nat := 1334203656731471179112897

theorem tailTrace_7795057 : CollatzResearch.WordTrace tailWord_7795057 prefixEnd_7795057 1334203656731471179112897 := by
  unfold tailWord_7795057
  simp only [CollatzResearch.WordTrace]
  refine ⟨284309085720847253591319425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189539390480564835727546283 284309085720847253591319425)
  ·
    refine ⟨213231814290635440193489569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284309085720847253591319425 213231814290635440193489569)
    ·
      refine ⟨159923860717976580145117177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213231814290635440193489569 159923860717976580145117177)
      ·
        refine ⟨119942895538482435108837883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159923860717976580145117177 119942895538482435108837883)
        ·
          refine ⟨179914343307723652663256825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119942895538482435108837883 179914343307723652663256825)
          ·
            refine ⟨134935757480792739497442619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179914343307723652663256825 134935757480792739497442619)
            ·
              refine ⟨202403636221189109246163929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134935757480792739497442619 202403636221189109246163929)
              ·
                refine ⟨151802727165891831934622947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202403636221189109246163929 151802727165891831934622947)
                ·
                  refine ⟨227704090748837747901934421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151802727165891831934622947 227704090748837747901934421)
                  ·
                    refine ⟨1334203656731471179112897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227704090748837747901934421 1334203656731471179112897)
                    ·
                      rfl

theorem cell23_7795057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_7795057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795057 prefixEnd_7795057 := by exact prefixLift 7795057
  have htrace : WordTrace (prefixWord ++ tailWord_7795057) baseStart_7795057 baseEnd_7795057 := by
    simpa [prefixWord, tailWord_7795057, baseEnd_7795057] using wordTrace_append hprefix tailTrace_7795057
  have hstable : (prefixWord ++ tailWord_7795057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795057).length < 2 ^ (prefixWord ++ tailWord_7795057).sum := by decide
  have hdescent : baseEnd_7795057 < baseStart_7795057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795082 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_7795082 : Nat := 118140960795 + 7795082 * 2 ^ 59
def prefixEnd_7795082 : Nat := 4983230072969 + 3 ^ 40 * 7795082 * 2
def baseEnd_7795082 : Nat := 1334207935736925313175359

theorem tailTrace_7795082 : CollatzResearch.WordTrace tailWord_7795082 prefixEnd_7795082 1334207935736925313175359 := by
  unfold tailWord_7795082
  simp only [CollatzResearch.WordTrace]
  refine ⟨71077499386439170715244875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189539998363837788573986333 71077499386439170715244875)
  ·
    refine ⟨106616249079658756072867313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71077499386439170715244875 106616249079658756072867313)
    ·
      refine ⟨79962186809744067054650485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106616249079658756072867313 79962186809744067054650485)
      ·
        refine ⟨7496455013413506286373483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79962186809744067054650485 7496455013413506286373483)
        ·
          refine ⟨11244682520120259429560225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7496455013413506286373483 11244682520120259429560225)
          ·
            refine ⟨8433511890090194572170169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11244682520120259429560225 8433511890090194572170169)
            ·
              refine ⟨6325133917567645929127627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8433511890090194572170169 6325133917567645929127627)
              ·
                refine ⟨9487700876351468893691441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325133917567645929127627 9487700876351468893691441)
                ·
                  refine ⟨7115775657263601670268581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9487700876351468893691441 7115775657263601670268581)
                  ·
                    refine ⟨1334207935736925313175359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7115775657263601670268581 1334207935736925313175359)
                    ·
                      rfl

theorem cell23_7795082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_7795082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795082 prefixEnd_7795082 := by exact prefixLift 7795082
  have htrace : WordTrace (prefixWord ++ tailWord_7795082) baseStart_7795082 baseEnd_7795082 := by
    simpa [prefixWord, tailWord_7795082, baseEnd_7795082] using wordTrace_append hprefix tailTrace_7795082
  have hstable : (prefixWord ++ tailWord_7795082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795082).length < 2 ^ (prefixWord ++ tailWord_7795082).sum := by decide
  have hdescent : baseEnd_7795082 < baseStart_7795082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795092 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_7795092 : Nat := 118140960795 + 7795092 * 2 ^ 59
def prefixEnd_7795092 : Nat := 4983230072969 + 3 ^ 40 * 7795092 * 2
def baseEnd_7795092 : Nat := 4002628942017320900401031

theorem tailTrace_7795092 : CollatzResearch.WordTrace tailWord_7795092 prefixEnd_7795092 4002628942017320900401031 := by
  unfold tailWord_7795092
  simp only [CollatzResearch.WordTrace]
  refine ⟨142155181137860227284421765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189540241517146969712562353 142155181137860227284421765)
  ·
    refine ⟨26654096463348792615829081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142155181137860227284421765 26654096463348792615829081)
    ·
      refine ⟨19990572347511594461871811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26654096463348792615829081 19990572347511594461871811)
      ·
        refine ⟨29985858521267391692807717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19990572347511594461871811 29985858521267391692807717)
        ·
          refine ⟨5622348472737635942401447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29985858521267391692807717 5622348472737635942401447)
          ·
            refine ⟨8433522709106453913602171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622348472737635942401447 8433522709106453913602171)
            ·
              refine ⟨12650284063659680870403257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433522709106453913602171 12650284063659680870403257)
              ·
                refine ⟨9487713047744760652802443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12650284063659680870403257 9487713047744760652802443)
                ·
                  refine ⟨14231569571617140979203665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9487713047744760652802443 14231569571617140979203665)
                  ·
                    refine ⟨10673677178712855734402749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14231569571617140979203665 10673677178712855734402749)
                    ·
                      refine ⟨4002628942017320900401031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10673677178712855734402749 4002628942017320900401031)
                      ·
                        rfl

theorem cell23_7795092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_7795092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795092 prefixEnd_7795092 := by exact prefixLift 7795092
  have htrace : WordTrace (prefixWord ++ tailWord_7795092) baseStart_7795092 baseEnd_7795092 := by
    simpa [prefixWord, tailWord_7795092, baseEnd_7795092] using wordTrace_append hprefix tailTrace_7795092
  have hstable : (prefixWord ++ tailWord_7795092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795092).length < 2 ^ (prefixWord ++ tailWord_7795092).sum := by decide
  have hdescent : baseEnd_7795092 < baseStart_7795092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795098 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2]
def baseStart_7795098 : Nat := 118140960795 + 7795098 * 2 ^ 59
def prefixEnd_7795098 : Nat := 4983230072969 + 3 ^ 40 * 7795098 * 2
def baseEnd_7795098 : Nat := 4002632022901247876926003

theorem tailTrace_7795098 : CollatzResearch.WordTrace tailWord_7795098 prefixEnd_7795098 4002632022901247876926003 := by
  unfold tailWord_7795098
  simp only [CollatzResearch.WordTrace]
  refine ⟨71077645278424679398390487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189540387409132478395707965 71077645278424679398390487)
  ·
    refine ⟨106616467917637019097585731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71077645278424679398390487 106616467917637019097585731)
    ·
      refine ⟨159924701876455528646378597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106616467917637019097585731 159924701876455528646378597)
      ·
        refine ⟨29985881601835411621195987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159924701876455528646378597 29985881601835411621195987)
        ·
          refine ⟨44978822402753117431793981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29985881601835411621195987 44978822402753117431793981)
          ·
            refine ⟨16867058401032419036922743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44978822402753117431793981 16867058401032419036922743)
            ·
              refine ⟨25300587601548628555384115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16867058401032419036922743 25300587601548628555384115)
              ·
                refine ⟨37950881402322942833076173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25300587601548628555384115 37950881402322942833076173)
                ·
                  refine ⟨14231580525871103562403565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37950881402322942833076173 14231580525871103562403565)
                  ·
                    refine ⟨5336842697201663835901337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14231580525871103562403565 5336842697201663835901337)
                    ·
                      refine ⟨4002632022901247876926003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336842697201663835901337 4002632022901247876926003)
                      ·
                        rfl

theorem cell23_7795098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_7795098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795098 prefixEnd_7795098 := by exact prefixLift 7795098
  have htrace : WordTrace (prefixWord ++ tailWord_7795098) baseStart_7795098 baseEnd_7795098 := by
    simpa [prefixWord, tailWord_7795098, baseEnd_7795098] using wordTrace_append hprefix tailTrace_7795098
  have hstable : (prefixWord ++ tailWord_7795098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795098).length < 2 ^ (prefixWord ++ tailWord_7795098).sum := by decide
  have hdescent : baseEnd_7795098 < baseStart_7795098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795201 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_7795201 : Nat := 118140960795 + 7795201 * 2 ^ 59
def prefixEnd_7795201 : Nat := 4983230072969 + 3 ^ 40 * 7795201 * 2
def baseEnd_7795201 : Nat := 4002684911408660973938029

theorem tailTrace_7795201 : CollatzResearch.WordTrace tailWord_7795201 prefixEnd_7795201 4002684911408660973938029 := by
  unfold tailWord_7795201
  simp only [CollatzResearch.WordTrace]
  refine ⟨284314337832325566184561457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189542891888217044123040971 284314337832325566184561457)
  ·
    refine ⟨213235753374244174638421093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284314337832325566184561457 213235753374244174638421093)
    ·
      refine ⟨39981703757670782744703955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213235753374244174638421093 39981703757670782744703955)
      ·
        refine ⟨59972555636506174117055933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39981703757670782744703955 59972555636506174117055933)
        ·
          refine ⟨22489708363689815293895975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59972555636506174117055933 22489708363689815293895975)
          ·
            refine ⟨33734562545534722940843963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22489708363689815293895975 33734562545534722940843963)
            ·
              refine ⟨50601843818302084411265945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33734562545534722940843963 50601843818302084411265945)
              ·
                refine ⟨37951382863726563308449459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50601843818302084411265945 37951382863726563308449459)
                ·
                  refine ⟨56927074295589844962674189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37951382863726563308449459 56927074295589844962674189)
                  ·
                    refine ⟨21347652860846191861002821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56927074295589844962674189 21347652860846191861002821)
                    ·
                      refine ⟨4002684911408660973938029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21347652860846191861002821 4002684911408660973938029)
                      ·
                        rfl

theorem cell23_7795201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_7795201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795201 prefixEnd_7795201 := by exact prefixLift 7795201
  have htrace : WordTrace (prefixWord ++ tailWord_7795201) baseStart_7795201 baseEnd_7795201 := by
    simpa [prefixWord, tailWord_7795201, baseEnd_7795201] using wordTrace_append hprefix tailTrace_7795201
  have hstable : (prefixWord ++ tailWord_7795201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795201).length < 2 ^ (prefixWord ++ tailWord_7795201).sum := by decide
  have hdescent : baseEnd_7795201 < baseStart_7795201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795221 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_7795221 : Nat := 118140960795 + 7795221 * 2 ^ 59
def prefixEnd_7795221 : Nat := 4983230072969 + 3 ^ 40 * 7795221 * 2
def baseEnd_7795221 : Nat := 4002695181021750895687937

theorem tailTrace_7795221 : CollatzResearch.WordTrace tailWord_7795221 prefixEnd_7795221 4002695181021750895687937 := by
  unfold tailWord_7795221
  simp only [CollatzResearch.WordTrace]
  refine ⟨284315067292253109600289517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189543378194835406400193011 284315067292253109600289517)
  ·
    refine ⟨106618150234594916100108569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284315067292253109600289517 106618150234594916100108569)
    ·
      refine ⟨79963612675946187075081427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106618150234594916100108569 79963612675946187075081427)
      ·
        refine ⟨119945419013919280612622141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79963612675946187075081427 119945419013919280612622141)
        ·
          refine ⟨44979532130219730229733303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119945419013919280612622141 44979532130219730229733303)
          ·
            refine ⟨67469298195329595344599955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44979532130219730229733303 67469298195329595344599955)
            ·
              refine ⟨101203947292994393016899933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67469298195329595344599955 101203947292994393016899933)
              ·
                refine ⟨37951480234872897381337475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101203947292994393016899933 37951480234872897381337475)
                ·
                  refine ⟨56927220352309346072006213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37951480234872897381337475 56927220352309346072006213)
                  ·
                    refine ⟨10673853816058002388501165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56927220352309346072006213 10673853816058002388501165)
                    ·
                      refine ⟨4002695181021750895687937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10673853816058002388501165 4002695181021750895687937)
                      ·
                        rfl

theorem cell23_7795221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_7795221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795221 prefixEnd_7795221 := by exact prefixLift 7795221
  have htrace : WordTrace (prefixWord ++ tailWord_7795221) baseStart_7795221 baseEnd_7795221 := by
    simpa [prefixWord, tailWord_7795221, baseEnd_7795221] using wordTrace_append hprefix tailTrace_7795221
  have hstable : (prefixWord ++ tailWord_7795221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795221).length < 2 ^ (prefixWord ++ tailWord_7795221).sum := by decide
  have hdescent : baseEnd_7795221 < baseStart_7795221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795244 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_7795244 : Nat := 118140960795 + 7795244 * 2 ^ 59
def prefixEnd_7795244 : Nat := 4983230072969 + 3 ^ 40 * 7795244 * 2
def baseEnd_7795244 : Nat := 4002706991076804305700331

theorem tailTrace_7795244 : CollatzResearch.WordTrace tailWord_7795244 prefixEnd_7795244 4002706991076804305700331 := by
  unfold tailWord_7795244
  simp only [CollatzResearch.WordTrace]
  refine ⟨142157953085584892264188393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189543937447446523018917857 142157953085584892264188393)
  ·
    refine ⟨106618464814188669198141295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142157953085584892264188393 106618464814188669198141295)
    ·
      refine ⟨159927697221283003797211943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106618464814188669198141295 159927697221283003797211943)
      ·
        refine ⟨239891545831924505695817915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159927697221283003797211943 239891545831924505695817915)
        ·
          refine ⟨359837318747886758543726873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239891545831924505695817915 359837318747886758543726873)
          ·
            refine ⟨269877989060915068907795155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359837318747886758543726873 269877989060915068907795155)
            ·
              refine ⟨404816983591372603361692733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269877989060915068907795155 404816983591372603361692733)
              ·
                refine ⟨151806368846764726260634775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404816983591372603361692733 151806368846764726260634775)
                ·
                  refine ⟨227709553270147089390952163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151806368846764726260634775 227709553270147089390952163)
                  ·
                    refine ⟨341564329905220634086428245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227709553270147089390952163 341564329905220634086428245)
                    ·
                      refine ⟨4002706991076804305700331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 341564329905220634086428245 4002706991076804305700331)
                      ·
                        rfl

theorem cell23_7795244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_7795244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795244 prefixEnd_7795244 := by exact prefixLift 7795244
  have htrace : WordTrace (prefixWord ++ tailWord_7795244) baseStart_7795244 baseEnd_7795244 := by
    simpa [prefixWord, tailWord_7795244, baseEnd_7795244] using wordTrace_append hprefix tailTrace_7795244
  have hstable : (prefixWord ++ tailWord_7795244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795244).length < 2 ^ (prefixWord ++ tailWord_7795244).sum := by decide
  have hdescent : baseEnd_7795244 < baseStart_7795244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795258 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 6]
def baseStart_7795258 : Nat := 118140960795 + 7795258 * 2 ^ 59
def prefixEnd_7795258 : Nat := 4983230072969 + 3 ^ 40 * 7795258 * 2
def baseEnd_7795258 : Nat := 444746019978440805658363

theorem tailTrace_7795258 : CollatzResearch.WordTrace tailWord_7795258 prefixEnd_7795258 444746019978440805658363 := by
  unfold tailWord_7795258
  simp only [CollatzResearch.WordTrace]
  refine ⟨71079104198279766229846607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189544277862079376612924285 71079104198279766229846607)
  ·
    refine ⟨106618656297419649344769911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71079104198279766229846607 106618656297419649344769911)
    ·
      refine ⟨159927984446129474017154867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106618656297419649344769911 159927984446129474017154867)
      ·
        refine ⟨239891976669194211025732301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159927984446129474017154867 239891976669194211025732301)
        ·
          refine ⟨89959491250947829134649613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239891976669194211025732301 89959491250947829134649613)
          ·
            refine ⟨33734809219105435925493605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89959491250947829134649613 33734809219105435925493605)
            ·
              refine ⟨6325276728582269236030051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33734809219105435925493605 6325276728582269236030051)
              ·
                refine ⟨9487915092873403854045077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325276728582269236030051 9487915092873403854045077)
                ·
                  refine ⟨444746019978440805658363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9487915092873403854045077 444746019978440805658363)
                  ·
                    rfl

theorem cell23_7795258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_7795258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795258 prefixEnd_7795258 := by exact prefixLift 7795258
  have htrace : WordTrace (prefixWord ++ tailWord_7795258) baseStart_7795258 baseEnd_7795258 := by
    simpa [prefixWord, tailWord_7795258, baseEnd_7795258] using wordTrace_append hprefix tailTrace_7795258
  have hstable : (prefixWord ++ tailWord_7795258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795258).length < 2 ^ (prefixWord ++ tailWord_7795258).sum := by decide
  have hdescent : baseEnd_7795258 < baseStart_7795258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795278 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_7795278 : Nat := 118140960795 + 7795278 * 2 ^ 59
def prefixEnd_7795278 : Nat := 4983230072969 + 3 ^ 40 * 7795278 * 2
def baseEnd_7795278 : Nat := 4002724449419057172675175

theorem tailTrace_7795278 : CollatzResearch.WordTrace tailWord_7795278 prefixEnd_7795278 4002724449419057172675175 := by
  unfold tailWord_7795278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35539643281630826041889311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189544764168697738890076325 35539643281630826041889311)
  ·
    refine ⟨53309464922446239062833967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35539643281630826041889311 53309464922446239062833967)
    ·
      refine ⟨79964197383669358594250951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53309464922446239062833967 79964197383669358594250951)
      ·
        refine ⟨119946296075504037891376427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79964197383669358594250951 119946296075504037891376427)
        ·
          refine ⟨179919444113256056837064641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119946296075504037891376427 179919444113256056837064641)
          ·
            refine ⟨134939583084942042627798481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179919444113256056837064641 134939583084942042627798481)
            ·
              refine ⟨101204687313706531970848861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134939583084942042627798481 101204687313706531970848861)
              ·
                refine ⟨37951757742639949489068323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101204687313706531970848861 37951757742639949489068323)
                ·
                  refine ⟨56927636613959924233602485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37951757742639949489068323 56927636613959924233602485)
                  ·
                    refine ⟨5336965932558742896900233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56927636613959924233602485 5336965932558742896900233)
                    ·
                      refine ⟨4002724449419057172675175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5336965932558742896900233 4002724449419057172675175)
                      ·
                        rfl

theorem cell23_7795278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_7795278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795278 prefixEnd_7795278 := by exact prefixLift 7795278
  have htrace : WordTrace (prefixWord ++ tailWord_7795278) baseStart_7795278 baseEnd_7795278 := by
    simpa [prefixWord, tailWord_7795278, baseEnd_7795278] using wordTrace_append hprefix tailTrace_7795278
  have hstable : (prefixWord ++ tailWord_7795278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795278).length < 2 ^ (prefixWord ++ tailWord_7795278).sum := by decide
  have hdescent : baseEnd_7795278 < baseStart_7795278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795311 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_7795311 : Nat := 118140960795 + 7795311 * 2 ^ 59
def prefixEnd_7795311 : Nat := 4983230072969 + 3 ^ 40 * 7795311 * 2
def baseEnd_7795311 : Nat := 4002741394280655543562523

theorem tailTrace_7795311 : CollatzResearch.WordTrace tailWord_7795311 prefixEnd_7795311 4002741394280655543562523 := by
  unfold tailWord_7795311
  simp only [CollatzResearch.WordTrace]
  refine ⟨284318349861927054971065787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189545566574618036647377191 284318349861927054971065787)
  ·
    refine ⟨426477524792890582456598681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284318349861927054971065787 426477524792890582456598681)
    ·
      refine ⟨319858143594667936842449011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426477524792890582456598681 319858143594667936842449011)
      ·
        refine ⟨479787215392001905263673517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319858143594667936842449011 479787215392001905263673517)
        ·
          refine ⟨179920205772000714473877569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479787215392001905263673517 179920205772000714473877569)
          ·
            refine ⟨134940154329000535855408177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179920205772000714473877569 134940154329000535855408177)
            ·
              refine ⟨101205115746750401891556133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134940154329000535855408177 101205115746750401891556133)
              ·
                refine ⟨18975959202515700354666775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101205115746750401891556133 18975959202515700354666775)
                ·
                  refine ⟨28463938803773550532000163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18975959202515700354666775 28463938803773550532000163)
                  ·
                    refine ⟨42695908205660325798000245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28463938803773550532000163 42695908205660325798000245)
                    ·
                      refine ⟨4002741394280655543562523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42695908205660325798000245 4002741394280655543562523)
                      ·
                        rfl

theorem cell23_7795311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_7795311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795311 prefixEnd_7795311 := by exact prefixLift 7795311
  have htrace : WordTrace (prefixWord ++ tailWord_7795311) baseStart_7795311 baseEnd_7795311 := by
    simpa [prefixWord, tailWord_7795311, baseEnd_7795311] using wordTrace_append hprefix tailTrace_7795311
  have hstable : (prefixWord ++ tailWord_7795311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795311).length < 2 ^ (prefixWord ++ tailWord_7795311).sum := by decide
  have hdescent : baseEnd_7795311 < baseStart_7795311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795328 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3]
def baseStart_7795328 : Nat := 118140960795 + 7795328 * 2 ^ 59
def prefixEnd_7795328 : Nat := 4983230072969 + 3 ^ 40 * 7795328 * 2
def baseEnd_7795328 : Nat := 4002750123451781977049945

theorem tailTrace_7795328 : CollatzResearch.WordTrace tailWord_7795328 prefixEnd_7795328 4002750123451781977049945 := by
  unfold tailWord_7795328
  simp only [CollatzResearch.WordTrace]
  refine ⟨142159484951432733437217319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189545979935243644582956425 142159484951432733437217319)
  ·
    refine ⟨213239227427149100155825979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142159484951432733437217319 213239227427149100155825979)
    ·
      refine ⟨319858841140723650233738969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213239227427149100155825979 319858841140723650233738969)
      ·
        refine ⟨239894130855542737675304227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319858841140723650233738969 239894130855542737675304227)
        ·
          refine ⟨359841196283314106512956341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239894130855542737675304227 359841196283314106512956341)
          ·
            refine ⟨33735112151560697485589657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359841196283314106512956341 33735112151560697485589657)
            ·
              refine ⟨25301334113670523114192243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33735112151560697485589657 25301334113670523114192243)
              ·
                refine ⟨37952001170505784671288365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25301334113670523114192243 37952001170505784671288365)
                ·
                  refine ⟨14232000438939669251733137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37952001170505784671288365 14232000438939669251733137)
                  ·
                    refine ⟨10674000329204751938799853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14232000438939669251733137 10674000329204751938799853)
                    ·
                      refine ⟨4002750123451781977049945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10674000329204751938799853 4002750123451781977049945)
                      ·
                        rfl

theorem cell23_7795328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_7795328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795328 prefixEnd_7795328 := by exact prefixLift 7795328
  have htrace : WordTrace (prefixWord ++ tailWord_7795328) baseStart_7795328 baseEnd_7795328 := by
    simpa [prefixWord, tailWord_7795328, baseEnd_7795328] using wordTrace_append hprefix tailTrace_7795328
  have hstable : (prefixWord ++ tailWord_7795328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795328).length < 2 ^ (prefixWord ++ tailWord_7795328).sum := by decide
  have hdescent : baseEnd_7795328 < baseStart_7795328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795348 : List Nat := [2, 4, 2, 2, 1, 2, 10]
def baseStart_7795348 : Nat := 118140960795 + 7795348 * 2 ^ 59
def prefixEnd_7795348 : Nat := 4983230072969 + 3 ^ 40 * 7795348 * 2
def baseEnd_7795348 : Nat := 49416794976109529614813

theorem tailTrace_7795348 : CollatzResearch.WordTrace tailWord_7795348 prefixEnd_7795348 49416794976109529614813 := by
  unfold tailWord_7795348
  simp only [CollatzResearch.WordTrace]
  refine ⟨142159849681396505145081349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189546466241862006860108465 142159849681396505145081349)
  ·
    refine ⟨26654971815261844714702753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142159849681396505145081349 26654971815261844714702753)
    ·
      refine ⟨19991228861446383536027065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26654971815261844714702753 19991228861446383536027065)
      ·
        refine ⟨14993421646084787652020299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19991228861446383536027065 14993421646084787652020299)
        ·
          refine ⟨22490132469127181478030449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14993421646084787652020299 22490132469127181478030449)
          ·
            refine ⟨16867599351845386108522837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22490132469127181478030449 16867599351845386108522837)
            ·
              refine ⟨49416794976109529614813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16867599351845386108522837 49416794976109529614813)
              ·
                rfl

theorem cell23_7795348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 10].length) (baseStart_7795348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795348 prefixEnd_7795348 := by exact prefixLift 7795348
  have htrace : WordTrace (prefixWord ++ tailWord_7795348) baseStart_7795348 baseEnd_7795348 := by
    simpa [prefixWord, tailWord_7795348, baseEnd_7795348] using wordTrace_append hprefix tailTrace_7795348
  have hstable : (prefixWord ++ tailWord_7795348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795348).length < 2 ^ (prefixWord ++ tailWord_7795348).sum := by decide
  have hdescent : baseEnd_7795348 < baseStart_7795348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795375 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 3]
def baseStart_7795375 : Nat := 118140960795 + 7795375 * 2 ^ 59
def prefixEnd_7795375 : Nat := 4983230072969 + 3 ^ 40 * 7795375 * 2
def baseEnd_7795375 : Nat := 4002774257042543293162229

theorem tailTrace_7795375 : CollatzResearch.WordTrace tailWord_7795375 prefixEnd_7795375 4002774257042543293162229 := by
  unfold tailWord_7795375
  simp only [CollatzResearch.WordTrace]
  refine ⟨284320684133695193901395579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189547122755796795934263719 284320684133695193901395579)
  ·
    refine ⟨426481026200542790852093369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284320684133695193901395579 426481026200542790852093369)
    ·
      refine ⟨319860769650407093139070027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426481026200542790852093369 319860769650407093139070027)
      ·
        refine ⟨479791154475610639708605041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319860769650407093139070027 479791154475610639708605041)
        ·
          refine ⟨359843365856707979781453781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479791154475610639708605041 359843365856707979781453781)
          ·
            refine ⟨8433828887266593276127823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 359843365856707979781453781 8433828887266593276127823)
            ·
              refine ⟨12650743330899889914191735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8433828887266593276127823 12650743330899889914191735)
              ·
                refine ⟨18976114996349834871287603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12650743330899889914191735 18976114996349834871287603)
                ·
                  refine ⟨28464172494524752306931405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18976114996349834871287603 28464172494524752306931405)
                  ·
                    refine ⟨10674064685446782115099277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28464172494524752306931405 10674064685446782115099277)
                    ·
                      refine ⟨4002774257042543293162229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10674064685446782115099277 4002774257042543293162229)
                      ·
                        rfl

theorem cell23_7795375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_7795375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795375 prefixEnd_7795375 := by exact prefixLift 7795375
  have htrace : WordTrace (prefixWord ++ tailWord_7795375) baseStart_7795375 baseEnd_7795375 := by
    simpa [prefixWord, tailWord_7795375, baseEnd_7795375] using wordTrace_append hprefix tailTrace_7795375
  have hstable : (prefixWord ++ tailWord_7795375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795375).length < 2 ^ (prefixWord ++ tailWord_7795375).sum := by decide
  have hdescent : baseEnd_7795375 < baseStart_7795375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795402 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_7795402 : Nat := 118140960795 + 7795402 * 2 ^ 59
def prefixEnd_7795402 : Nat := 4983230072969 + 3 ^ 40 * 7795402 * 2
def baseEnd_7795402 : Nat := 4002788121020214687524605

theorem tailTrace_7795402 : CollatzResearch.WordTrace tailWord_7795402 prefixEnd_7795402 4002788121020214687524605 := by
  unfold tailWord_7795402
  simp only [CollatzResearch.WordTrace]
  refine ⟨71080417226149344378157115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189547779269731585008418973 71080417226149344378157115)
  ·
    refine ⟨106620625839224016567235673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71080417226149344378157115 106620625839224016567235673)
    ·
      refine ⟨79965469379418012425426755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106620625839224016567235673 79965469379418012425426755)
      ·
        refine ⟨119948204069127018638140133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79965469379418012425426755 119948204069127018638140133)
        ·
          refine ⟨22490288262961315994651275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119948204069127018638140133 22490288262961315994651275)
          ·
            refine ⟨33735432394441973991976913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22490288262961315994651275 33735432394441973991976913)
            ·
              refine ⟨25301574295831480493982685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33735432394441973991976913 25301574295831480493982685)
              ·
                refine ⟨9488090360936805185243507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25301574295831480493982685 9488090360936805185243507)
                ·
                  refine ⟨14232135541405207777865261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9488090360936805185243507 14232135541405207777865261)
                  ·
                    refine ⟨5337050828026952916699473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14232135541405207777865261 5337050828026952916699473)
                    ·
                      refine ⟨4002788121020214687524605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337050828026952916699473 4002788121020214687524605)
                      ·
                        rfl

theorem cell23_7795402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_7795402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795402 prefixEnd_7795402 := by exact prefixLift 7795402
  have htrace : WordTrace (prefixWord ++ tailWord_7795402) baseStart_7795402 baseEnd_7795402 := by
    simpa [prefixWord, tailWord_7795402, baseEnd_7795402] using wordTrace_append hprefix tailTrace_7795402
  have hstable : (prefixWord ++ tailWord_7795402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795402).length < 2 ^ (prefixWord ++ tailWord_7795402).sum := by decide
  have hdescent : baseEnd_7795402 < baseStart_7795402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795418 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_7795418 : Nat := 118140960795 + 7795418 * 2 ^ 59
def prefixEnd_7795418 : Nat := 4983230072969 + 3 ^ 40 * 7795418 * 2
def baseEnd_7795418 : Nat := 4002796336710686624924531

theorem tailTrace_7795418 : CollatzResearch.WordTrace tailWord_7795418 prefixEnd_7795418 4002796336710686624924531 := by
  unfold tailWord_7795418
  simp only [CollatzResearch.WordTrace]
  refine ⟨71080563118134853061302727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189548168315026274830140605 71080563118134853061302727)
  ·
    refine ⟨106620844677202279591954091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71080563118134853061302727 106620844677202279591954091)
    ·
      refine ⟨159931267015803419387931137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106620844677202279591954091 159931267015803419387931137)
      ·
        refine ⟨119948450261852564540948353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159931267015803419387931137 119948450261852564540948353)
        ·
          refine ⟨89961337696389423405711265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119948450261852564540948353 89961337696389423405711265)
          ·
            refine ⟨67471003272292067554283449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89961337696389423405711265 67471003272292067554283449)
            ·
              refine ⟨50603252454219050665712587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67471003272292067554283449 50603252454219050665712587)
              ·
                refine ⟨75904878681328575998568881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50603252454219050665712587 75904878681328575998568881)
                ·
                  refine ⟨56928659010996431998926661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75904878681328575998568881 56928659010996431998926661)
                  ·
                    refine ⟨10674123564561830999798749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56928659010996431998926661 10674123564561830999798749)
                    ·
                      refine ⟨4002796336710686624924531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10674123564561830999798749 4002796336710686624924531)
                      ·
                        rfl

theorem cell23_7795418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_7795418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795418 prefixEnd_7795418 := by exact prefixLift 7795418
  have htrace : WordTrace (prefixWord ++ tailWord_7795418) baseStart_7795418 baseEnd_7795418 := by
    simpa [prefixWord, tailWord_7795418, baseEnd_7795418] using wordTrace_append hprefix tailTrace_7795418
  have hstable : (prefixWord ++ tailWord_7795418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795418).length < 2 ^ (prefixWord ++ tailWord_7795418).sum := by decide
  have hdescent : baseEnd_7795418 < baseStart_7795418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795451 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 5, 7]
def baseStart_7795451 : Nat := 118140960795 + 7795451 * 2 ^ 59
def prefixEnd_7795451 : Nat := 4983230072969 + 3 ^ 40 * 7795451 * 2
def baseEnd_7795451 : Nat := 1334271093857428331937293

theorem tailTrace_7795451 : CollatzResearch.WordTrace tailWord_7795451 prefixEnd_7795451 1334271093857428331937293 := by
  unfold tailWord_7795451
  simp only [CollatzResearch.WordTrace]
  refine ⟨284323456081419858881162207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189548970720946572587441471 284323456081419858881162207)
  ·
    refine ⟨426485184122129788321743311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284323456081419858881162207 426485184122129788321743311)
    ·
      refine ⟨639727776183194682482614967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426485184122129788321743311 639727776183194682482614967)
      ·
        refine ⟨959591664274792023723922451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639727776183194682482614967 959591664274792023723922451)
        ·
          refine ⟨1439387496412188035585883677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959591664274792023723922451 1439387496412188035585883677)
          ·
            refine ⟨539770311154570513344706379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1439387496412188035585883677 539770311154570513344706379)
            ·
              refine ⟨809655466731855770017059569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539770311154570513344706379 809655466731855770017059569)
              ·
                refine ⟨607241600048891827512794677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809655466731855770017059569 607241600048891827512794677)
                ·
                  refine ⟨56928900004583608829324501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 607241600048891827512794677 56928900004583608829324501)
                  ·
                    refine ⟨1334271093857428331937293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56928900004583608829324501 1334271093857428331937293)
                    ·
                      rfl

theorem cell23_7795451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_7795451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795451 prefixEnd_7795451 := by exact prefixLift 7795451
  have htrace : WordTrace (prefixWord ++ tailWord_7795451) baseStart_7795451 baseEnd_7795451 := by
    simpa [prefixWord, tailWord_7795451, baseEnd_7795451] using wordTrace_append hprefix tailTrace_7795451
  have hstable : (prefixWord ++ tailWord_7795451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795451).length < 2 ^ (prefixWord ++ tailWord_7795451).sum := by decide
  have hdescent : baseEnd_7795451 < baseStart_7795451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795502 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_7795502 : Nat := 118140960795 + 7795502 * 2 ^ 59
def prefixEnd_7795502 : Nat := 4983230072969 + 3 ^ 40 * 7795502 * 2
def baseEnd_7795502 : Nat := 1334279823028554765424715

theorem tailTrace_7795502 : CollatzResearch.WordTrace tailWord_7795502 prefixEnd_7795502 1334279823028554765424715 := by
  unfold tailWord_7795502
  simp only [CollatzResearch.WordTrace]
  refine ⟨35540664525529386823908595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189550210802823396394179173 35540664525529386823908595)
  ·
    refine ⟨53310996788294080235862893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35540664525529386823908595 53310996788294080235862893)
    ·
      refine ⟨19991623795610280088448585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53310996788294080235862893 19991623795610280088448585)
      ·
        refine ⟨14993717846707710066336439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19991623795610280088448585 14993717846707710066336439)
        ·
          refine ⟨22490576770061565099504659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14993717846707710066336439 22490576770061565099504659)
          ·
            refine ⟨33735865155092347649256989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22490576770061565099504659 33735865155092347649256989)
            ·
              refine ⟨12650949433159630368471371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33735865155092347649256989 12650949433159630368471371)
              ·
                refine ⟨18976424149739445552707057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12650949433159630368471371 18976424149739445552707057)
                ·
                  refine ⟨14232318112304584164530293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18976424149739445552707057 14232318112304584164530293)
                  ·
                    refine ⟨1334279823028554765424715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14232318112304584164530293 1334279823028554765424715)
                    ·
                      rfl

theorem cell23_7795502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_7795502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795502 prefixEnd_7795502 := by exact prefixLift 7795502
  have htrace : WordTrace (prefixWord ++ tailWord_7795502) baseStart_7795502 baseEnd_7795502 := by
    simpa [prefixWord, tailWord_7795502, baseEnd_7795502] using wordTrace_append hprefix tailTrace_7795502
  have hstable : (prefixWord ++ tailWord_7795502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795502).length < 2 ^ (prefixWord ++ tailWord_7795502).sum := by decide
  have hdescent : baseEnd_7795502 < baseStart_7795502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795505 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 1, 6, 2]
def baseStart_7795505 : Nat := 118140960795 + 7795505 * 2 ^ 59
def prefixEnd_7795505 : Nat := 4983230072969 + 3 ^ 40 * 7795505 * 2
def baseEnd_7795505 : Nat := 4002841009527627784536631

theorem tailTrace_7795505 : CollatzResearch.WordTrace tailWord_7795505 prefixEnd_7795505 4002841009527627784536631 := by
  unfold tailWord_7795505
  simp only [CollatzResearch.WordTrace]
  refine ⟨284325425623224226103627969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189550283748816150735751979 284325425623224226103627969)
  ·
    refine ⟨213244069217418169577720977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284325425623224226103627969 213244069217418169577720977)
    ·
      refine ⟨159933051913063627183290733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213244069217418169577720977 159933051913063627183290733)
      ·
        refine ⟨59974894467398860193734025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159933051913063627183290733 59974894467398860193734025)
        ·
          refine ⟨44981170850549145145300519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59974894467398860193734025 44981170850549145145300519)
          ·
            refine ⟨67471756275823717717950779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44981170850549145145300519 67471756275823717717950779)
            ·
              refine ⟨101207634413735576576926169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67471756275823717717950779 101207634413735576576926169)
              ·
                refine ⟨75905725810301682432694627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101207634413735576576926169 75905725810301682432694627)
                ·
                  refine ⟨113858588715452523649041941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75905725810301682432694627 113858588715452523649041941)
                  ·
                    refine ⟨5337121346036837046048841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113858588715452523649041941 5337121346036837046048841)
                    ·
                      refine ⟨4002841009527627784536631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337121346036837046048841 4002841009527627784536631)
                      ·
                        rfl

theorem cell23_7795505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_7795505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795505 prefixEnd_7795505 := by exact prefixLift 7795505
  have htrace : WordTrace (prefixWord ++ tailWord_7795505) baseStart_7795505 baseEnd_7795505 := by
    simpa [prefixWord, tailWord_7795505, baseEnd_7795505] using wordTrace_append hprefix tailTrace_7795505
  have hstable : (prefixWord ++ tailWord_7795505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795505).length < 2 ^ (prefixWord ++ tailWord_7795505).sum := by decide
  have hdescent : baseEnd_7795505 < baseStart_7795505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795528 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 8]
def baseStart_7795528 : Nat := 118140960795 + 7795528 * 2 ^ 59
def prefixEnd_7795528 : Nat := 4983230072969 + 3 ^ 40 * 7795528 * 2
def baseEnd_7795528 : Nat := 444761424398075688283225

theorem tailTrace_7795528 : CollatzResearch.WordTrace tailWord_7795528 prefixEnd_7795528 444761424398075688283225 := by
  unfold tailWord_7795528
  simp only [CollatzResearch.WordTrace]
  refine ⟨142163132251070450515857619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189550843001427267354476825 142163132251070450515857619)
  ·
    refine ⟨213244698376605675773786429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142163132251070450515857619 213244698376605675773786429)
    ·
      refine ⟨79966761891227128415169911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213244698376605675773786429 79966761891227128415169911)
      ·
        refine ⟨119950142836840692622754867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79966761891227128415169911 119950142836840692622754867)
        ·
          refine ⟨179925214255261038934132301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119950142836840692622754867 179925214255261038934132301)
          ·
            refine ⟨67471955345722889600299613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179925214255261038934132301 67471955345722889600299613)
            ·
              refine ⟨25301983254646083600112355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67471955345722889600299613 25301983254646083600112355)
              ·
                refine ⟨37952974881969125400168533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25301983254646083600112355 37952974881969125400168533)
                ·
                  refine ⟨444761424398075688283225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37952974881969125400168533 444761424398075688283225)
                  ·
                    rfl

theorem cell23_7795528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 8].length) (baseStart_7795528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795528 prefixEnd_7795528 := by exact prefixLift 7795528
  have htrace : WordTrace (prefixWord ++ tailWord_7795528) baseStart_7795528 baseEnd_7795528 := by
    simpa [prefixWord, tailWord_7795528, baseEnd_7795528] using wordTrace_append hprefix tailTrace_7795528
  have hstable : (prefixWord ++ tailWord_7795528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795528).length < 2 ^ (prefixWord ++ tailWord_7795528).sum := by decide
  have hdescent : baseEnd_7795528 < baseStart_7795528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795532 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_7795532 : Nat := 118140960795 + 7795532 * 2 ^ 59
def prefixEnd_7795532 : Nat := 4983230072969 + 3 ^ 40 * 7795532 * 2
def baseEnd_7795532 : Nat := 1334284957835099726299669

theorem tailTrace_7795532 : CollatzResearch.WordTrace tailWord_7795532 prefixEnd_7795532 1334284957835099726299669 := by
  unfold tailWord_7795532
  simp only [CollatzResearch.WordTrace]
  refine ⟨142163205197063204857430425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189550940262750939809907233 142163205197063204857430425)
  ·
    refine ⟨106622403897797403643072819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142163205197063204857430425 106622403897797403643072819)
    ·
      refine ⟨159933605846696105464609229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106622403897797403643072819 159933605846696105464609229)
      ·
        refine ⟨59975102192511039549228461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159933605846696105464609229 59975102192511039549228461)
        ·
          refine ⟨22490663322191639830960673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59975102192511039549228461 22490663322191639830960673)
          ·
            refine ⟨16867997491643729873220505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22490663322191639830960673 16867997491643729873220505)
            ·
              refine ⟨12650998118732797404915379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16867997491643729873220505 12650998118732797404915379)
              ·
                refine ⟨18976497178099196107373069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12650998118732797404915379 18976497178099196107373069)
                ·
                  refine ⟨7116186441787198540264901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18976497178099196107373069 7116186441787198540264901)
                  ·
                    refine ⟨1334284957835099726299669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7116186441787198540264901 1334284957835099726299669)
                    ·
                      rfl

theorem cell23_7795532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_7795532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795532 prefixEnd_7795532 := by exact prefixLift 7795532
  have htrace : WordTrace (prefixWord ++ tailWord_7795532) baseStart_7795532 baseEnd_7795532 := by
    simpa [prefixWord, tailWord_7795532, baseEnd_7795532] using wordTrace_append hprefix tailTrace_7795532
  have hstable : (prefixWord ++ tailWord_7795532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795532).length < 2 ^ (prefixWord ++ tailWord_7795532).sum := by decide
  have hdescent : baseEnd_7795532 < baseStart_7795532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795589 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_7795589 : Nat := 118140960795 + 7795589 * 2 ^ 59
def prefixEnd_7795589 : Nat := 4983230072969 + 3 ^ 40 * 7795589 * 2
def baseEnd_7795589 : Nat := 4002884141902605455886245

theorem tailTrace_7795589 : CollatzResearch.WordTrace tailWord_7795589 prefixEnd_7795589 4002884141902605455886245 := by
  unfold tailWord_7795589
  simp only [CollatzResearch.WordTrace]
  refine ⟨284328489354919908449685821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189552326236613272299790547 284328489354919908449685821)
  ·
    refine ⟨106623183508094965668632183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284328489354919908449685821 106623183508094965668632183)
    ·
      refine ⟨159934775262142448502948275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106623183508094965668632183 159934775262142448502948275)
      ·
        refine ⟨239902162893213672754422413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159934775262142448502948275 239902162893213672754422413)
        ·
          refine ⟨89963311084955127282908405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239902162893213672754422413 89963311084955127282908405)
          ·
            refine ⟨8434060414214543182772663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89963311084955127282908405 8434060414214543182772663)
            ·
              refine ⟨12651090621321814774158995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434060414214543182772663 12651090621321814774158995)
              ·
                refine ⟨18976635931982722161238493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12651090621321814774158995 18976635931982722161238493)
                ·
                  refine ⟨7116238474493520810464435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18976635931982722161238493 7116238474493520810464435)
                  ·
                    refine ⟨10674357711740281215696653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7116238474493520810464435 10674357711740281215696653)
                    ·
                      refine ⟨4002884141902605455886245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10674357711740281215696653 4002884141902605455886245)
                      ·
                        rfl

theorem cell23_7795589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_7795589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795589 prefixEnd_7795589 := by exact prefixLift 7795589
  have htrace : WordTrace (prefixWord ++ tailWord_7795589) baseStart_7795589 baseEnd_7795589 := by
    simpa [prefixWord, tailWord_7795589, baseEnd_7795589] using wordTrace_append hprefix tailTrace_7795589
  have hstable : (prefixWord ++ tailWord_7795589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795589).length < 2 ^ (prefixWord ++ tailWord_7795589).sum := by decide
  have hdescent : baseEnd_7795589 < baseStart_7795589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795625 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_7795625 : Nat := 118140960795 + 7795625 * 2 ^ 59
def prefixEnd_7795625 : Nat := 4983230072969 + 3 ^ 40 * 7795625 * 2
def baseEnd_7795625 : Nat := 4002902627206167315036079

theorem tailTrace_7795625 : CollatzResearch.WordTrace tailWord_7795625 prefixEnd_7795625 4002902627206167315036079 := by
  unfold tailWord_7795625
  simp only [CollatzResearch.WordTrace]
  refine ⟨284329802382789486597996329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189553201588526324398664219 284329802382789486597996329)
  ·
    refine ⟨213247351787092114948497247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284329802382789486597996329 213247351787092114948497247)
    ·
      refine ⟨319871027680638172422745871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213247351787092114948497247 319871027680638172422745871)
      ·
        refine ⟨479806541520957258634118807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319871027680638172422745871 479806541520957258634118807)
        ·
          refine ⟨719709812281435887951178211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479806541520957258634118807 719709812281435887951178211)
          ·
            refine ⟨1079564718422153831926767317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719709812281435887951178211 1079564718422153831926767317)
            ·
              refine ⟨25302298088019230435783609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1079564718422153831926767317 25302298088019230435783609)
              ·
                refine ⟨18976723566014422826837707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25302298088019230435783609 18976723566014422826837707)
                ·
                  refine ⟨28465085349021634240256561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18976723566014422826837707 28465085349021634240256561)
                  ·
                    refine ⟨21348814011766225680192421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28465085349021634240256561 21348814011766225680192421)
                    ·
                      refine ⟨4002902627206167315036079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21348814011766225680192421 4002902627206167315036079)
                      ·
                        rfl

theorem cell23_7795625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_7795625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795625 prefixEnd_7795625 := by exact prefixLift 7795625
  have htrace : WordTrace (prefixWord ++ tailWord_7795625) baseStart_7795625 baseEnd_7795625 := by
    simpa [prefixWord, tailWord_7795625, baseEnd_7795625] using wordTrace_append hprefix tailTrace_7795625
  have hstable : (prefixWord ++ tailWord_7795625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795625).length < 2 ^ (prefixWord ++ tailWord_7795625).sum := by decide
  have hdescent : baseEnd_7795625 < baseStart_7795625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795662 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_7795662 : Nat := 118140960795 + 7795662 * 2 ^ 59
def prefixEnd_7795662 : Nat := 4983230072969 + 3 ^ 40 * 7795662 * 2
def baseEnd_7795662 : Nat := 4002921625990383670273409

theorem tailTrace_7795662 : CollatzResearch.WordTrace tailWord_7795662 prefixEnd_7795662 4002921625990383670273409 := by
  unfold tailWord_7795662
  simp only [CollatzResearch.WordTrace]
  refine ⟨35541393985456930239636655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189554101255770294611395493 35541393985456930239636655)
  ·
    refine ⟨53312090978185395359454983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35541393985456930239636655 53312090978185395359454983)
    ·
      refine ⟨79968136467278093039182475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53312090978185395359454983 79968136467278093039182475)
      ·
        refine ⟨119952204700917139558773713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79968136467278093039182475 119952204700917139558773713)
        ·
          refine ⟨89964153525687854669080285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119952204700917139558773713 89964153525687854669080285)
          ·
            refine ⟨33736557572132945500905107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89964153525687854669080285 33736557572132945500905107)
            ·
              refine ⟨50604836358199418251357661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33736557572132945500905107 50604836358199418251357661)
              ·
                refine ⟨18976813634324781844259123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50604836358199418251357661 18976813634324781844259123)
                ·
                  refine ⟨28465220451487172766388685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18976813634324781844259123 28465220451487172766388685)
                  ·
                    refine ⟨10674457669307689787395757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28465220451487172766388685 10674457669307689787395757)
                    ·
                      refine ⟨4002921625990383670273409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10674457669307689787395757 4002921625990383670273409)
                      ·
                        rfl

theorem cell23_7795662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_7795662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795662 prefixEnd_7795662 := by exact prefixLift 7795662
  have htrace : WordTrace (prefixWord ++ tailWord_7795662) baseStart_7795662 baseEnd_7795662 := by
    simpa [prefixWord, tailWord_7795662, baseEnd_7795662] using wordTrace_append hprefix tailTrace_7795662
  have hstable : (prefixWord ++ tailWord_7795662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795662).length < 2 ^ (prefixWord ++ tailWord_7795662).sum := by decide
  have hdescent : baseEnd_7795662 < baseStart_7795662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795695 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 2, 6]
def baseStart_7795695 : Nat := 118140960795 + 7795695 * 2 ^ 59
def prefixEnd_7795695 : Nat := 4983230072969 + 3 ^ 40 * 7795695 * 2
def baseEnd_7795695 : Nat := 1334312856950660680386919

theorem tailTrace_7795695 : CollatzResearch.WordTrace tailWord_7795695 prefixEnd_7795695 1334312856950660680386919 := by
  unfold tailWord_7795695
  simp only [CollatzResearch.WordTrace]
  refine ⟨284332355492535888553044539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189554903661690592368696359 284332355492535888553044539)
  ·
    refine ⟨426498533238803832829566809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284332355492535888553044539 426498533238803832829566809)
    ·
      refine ⟨319873899929102874622175107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426498533238803832829566809 319873899929102874622175107)
      ·
        refine ⟨479810849893654311933262661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319873899929102874622175107 479810849893654311933262661)
        ·
          refine ⟨89964534355060183487486749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 479810849893654311933262661 89964534355060183487486749)
          ·
            refine ⟨33736700383147568807807531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89964534355060183487486749 33736700383147568807807531)
            ·
              refine ⟨50605050574721353211711297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33736700383147568807807531 50605050574721353211711297)
              ·
                refine ⟨37953787931041014908783473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50605050574721353211711297 37953787931041014908783473)
                ·
                  refine ⟨28465340948280761181587605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37953787931041014908783473 28465340948280761181587605)
                  ·
                    refine ⟨1334312856950660680386919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28465340948280761181587605 1334312856950660680386919)
                    ·
                      rfl

theorem cell23_7795695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_7795695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795695 prefixEnd_7795695 := by exact prefixLift 7795695
  have htrace : WordTrace (prefixWord ++ tailWord_7795695) baseStart_7795695 baseEnd_7795695 := by
    simpa [prefixWord, tailWord_7795695, baseEnd_7795695] using wordTrace_append hprefix tailTrace_7795695
  have hstable : (prefixWord ++ tailWord_7795695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795695).length < 2 ^ (prefixWord ++ tailWord_7795695).sum := by decide
  have hdescent : baseEnd_7795695 < baseStart_7795695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795789 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7795789 : Nat := 118140960795 + 7795789 * 2 ^ 59
def prefixEnd_7795789 : Nat := 4983230072969 + 3 ^ 40 * 7795789 * 2
def baseEnd_7795789 : Nat := 1334328946011168224461775

theorem tailTrace_7795789 : CollatzResearch.WordTrace tailWord_7795789 prefixEnd_7795789 1334328946011168224461775 := by
  unfold tailWord_7795789
  simp only [CollatzResearch.WordTrace]
  refine ⟨284335783954195342606966421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189557189302796895071310947 284335783954195342606966421)
  ·
    refine ⟨13328239872852906684701551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 284335783954195342606966421 13328239872852906684701551)
    ·
      refine ⟨19992359809279360027052327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13328239872852906684701551 19992359809279360027052327)
      ·
        refine ⟨29988539713919040040578491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19992359809279360027052327 29988539713919040040578491)
        ·
          refine ⟨44982809570878560060867737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29988539713919040040578491 44982809570878560060867737)
          ·
            refine ⟨33737107178158920045650803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44982809570878560060867737 33737107178158920045650803)
            ·
              refine ⟨50605660767238380068476205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33737107178158920045650803 50605660767238380068476205)
              ·
                refine ⟨18977122787714392525678577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50605660767238380068476205 18977122787714392525678577)
                ·
                  refine ⟨14232842090785794394258933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18977122787714392525678577 14232842090785794394258933)
                  ·
                    refine ⟨1334328946011168224461775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14232842090785794394258933 1334328946011168224461775)
                    ·
                      rfl

theorem cell23_7795789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7795789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795789 prefixEnd_7795789 := by exact prefixLift 7795789
  have htrace : WordTrace (prefixWord ++ tailWord_7795789) baseStart_7795789 baseEnd_7795789 := by
    simpa [prefixWord, tailWord_7795789, baseEnd_7795789] using wordTrace_append hprefix tailTrace_7795789
  have hstable : (prefixWord ++ tailWord_7795789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795789).length < 2 ^ (prefixWord ++ tailWord_7795789).sum := by decide
  have hdescent : baseEnd_7795789 < baseStart_7795789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795795 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5]
def baseStart_7795795 : Nat := 118140960795 + 7795795 * 2 ^ 59
def prefixEnd_7795795 : Nat := 4983230072969 + 3 ^ 40 * 7795795 * 2
def baseEnd_7795795 : Nat := 4002989918917431649910297

theorem tailTrace_7795795 : CollatzResearch.WordTrace tailWord_7795795 prefixEnd_7795795 4002989918917431649910297 := by
  unfold tailWord_7795795
  simp only [CollatzResearch.WordTrace]
  refine ⟨284336002792173605631684839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189557335194782403754456559 284336002792173605631684839)
  ·
    refine ⟨426504004188260408447527259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284336002792173605631684839 426504004188260408447527259)
    ·
      refine ⟨639756006282390612671290889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426504004188260408447527259 639756006282390612671290889)
      ·
        refine ⟨479817004711792959503468167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639756006282390612671290889 479817004711792959503468167)
        ·
          refine ⟨719725507067689439255202251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479817004711792959503468167 719725507067689439255202251)
          ·
            refine ⟨1079588260601534158882803377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719725507067689439255202251 1079588260601534158882803377)
            ·
              refine ⟨809691195451150619162102533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079588260601534158882803377 809691195451150619162102533)
              ·
                refine ⟨151817099147090741092894225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 809691195451150619162102533 151817099147090741092894225)
                ·
                  refine ⟨113862824360318055819670669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151817099147090741092894225 113862824360318055819670669)
                  ·
                    refine ⟨42698559135119270932376501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113862824360318055819670669 42698559135119270932376501)
                    ·
                      refine ⟨4002989918917431649910297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42698559135119270932376501 4002989918917431649910297)
                      ·
                        rfl

theorem cell23_7795795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_7795795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795795 prefixEnd_7795795 := by exact prefixLift 7795795
  have htrace : WordTrace (prefixWord ++ tailWord_7795795) baseStart_7795795 baseEnd_7795795 := by
    simpa [prefixWord, tailWord_7795795, baseEnd_7795795] using wordTrace_append hprefix tailTrace_7795795
  have hstable : (prefixWord ++ tailWord_7795795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795795).length < 2 ^ (prefixWord ++ tailWord_7795795).sum := by decide
  have hdescent : baseEnd_7795795 < baseStart_7795795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795802 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_7795802 : Nat := 118140960795 + 7795802 * 2 ^ 59
def prefixEnd_7795802 : Nat := 4983230072969 + 3 ^ 40 * 7795802 * 2
def baseEnd_7795802 : Nat := 1334331171094004374174255

theorem tailTrace_7795802 : CollatzResearch.WordTrace tailWord_7795802 prefixEnd_7795802 1334331171094004374174255 := by
  unfold tailWord_7795802
  simp only [CollatzResearch.WordTrace]
  refine ⟨71084064525787061456797415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189557505402098830551459773 71084064525787061456797415)
  ·
    refine ⟨106626096788680592185196123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71084064525787061456797415 106626096788680592185196123)
    ·
      refine ⟨159939145183020888277794185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106626096788680592185196123 159939145183020888277794185)
      ·
        refine ⟨119954358887265666208345639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159939145183020888277794185 119954358887265666208345639)
        ·
          refine ⟨179931538330898499312518459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119954358887265666208345639 179931538330898499312518459)
          ·
            refine ⟨269897307496347748968777689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179931538330898499312518459 269897307496347748968777689)
            ·
              refine ⟨202422980622260811726583267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269897307496347748968777689 202422980622260811726583267)
              ·
                refine ⟨303634470933391217589874901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202422980622260811726583267 303634470933391217589874901)
                ·
                  refine ⟨7116432912501356662262693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 303634470933391217589874901 7116432912501356662262693)
                  ·
                    refine ⟨1334331171094004374174255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7116432912501356662262693 1334331171094004374174255)
                    ·
                      rfl

theorem cell23_7795802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_7795802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795802 prefixEnd_7795802 := by exact prefixLift 7795802
  have htrace : WordTrace (prefixWord ++ tailWord_7795802) baseStart_7795802 baseEnd_7795802 := by
    simpa [prefixWord, tailWord_7795802, baseEnd_7795802] using wordTrace_append hprefix tailTrace_7795802
  have hstable : (prefixWord ++ tailWord_7795802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795802).length < 2 ^ (prefixWord ++ tailWord_7795802).sum := by decide
  have hdescent : baseEnd_7795802 < baseStart_7795802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795812 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_7795812 : Nat := 118140960795 + 7795812 * 2 ^ 59
def prefixEnd_7795812 : Nat := 4983230072969 + 3 ^ 40 * 7795812 * 2
def baseEnd_7795812 : Nat := 4002998648088558083397719

theorem tailTrace_7795812 : CollatzResearch.WordTrace tailWord_7795812 prefixEnd_7795812 4002998648088558083397719 := by
  unfold tailWord_7795812
  simp only [CollatzResearch.WordTrace]
  refine ⟨142168311416556008767526845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189557748555408011690035793 142168311416556008767526845)
  ·
    refine ⟨53313116781208503287822567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142168311416556008767526845 53313116781208503287822567)
    ·
      refine ⟨79969675171812754931733851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53313116781208503287822567 79969675171812754931733851)
      ·
        refine ⟨119954512757719132397600777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79969675171812754931733851 119954512757719132397600777)
        ·
          refine ⟨89965884568289349298200583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119954512757719132397600777 89965884568289349298200583)
          ·
            refine ⟨134948826852434023947300875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89965884568289349298200583 134948826852434023947300875)
            ·
              refine ⟨202423240278651035920951313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134948826852434023947300875 202423240278651035920951313)
              ·
                refine ⟨151817430208988276940713485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202423240278651035920951313 151817430208988276940713485)
                ·
                  refine ⟨56931536328370603852767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151817430208988276940713485 56931536328370603852767557)
                  ·
                    refine ⟨10674663061569488222393917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56931536328370603852767557 10674663061569488222393917)
                    ·
                      refine ⟨4002998648088558083397719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10674663061569488222393917 4002998648088558083397719)
                      ·
                        rfl

theorem cell23_7795812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_7795812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795812 prefixEnd_7795812 := by exact prefixLift 7795812
  have htrace : WordTrace (prefixWord ++ tailWord_7795812) baseStart_7795812 baseEnd_7795812 := by
    simpa [prefixWord, tailWord_7795812, baseEnd_7795812] using wordTrace_append hprefix tailTrace_7795812
  have hstable : (prefixWord ++ tailWord_7795812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795812).length < 2 ^ (prefixWord ++ tailWord_7795812).sum := by decide
  have hdescent : baseEnd_7795812 < baseStart_7795812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795832 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 6]
def baseStart_7795832 : Nat := 118140960795 + 7795832 * 2 ^ 59
def prefixEnd_7795832 : Nat := 4983230072969 + 3 ^ 40 * 7795832 * 2
def baseEnd_7795832 : Nat := 444778768633516445016403

theorem tailTrace_7795832 : CollatzResearch.WordTrace tailWord_7795832 prefixEnd_7795832 444778768633516445016403 := by
  unfold tailWord_7795832
  simp only [CollatzResearch.WordTrace]
  refine ⟨142168676146519780475390875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189558234862026373967187833 142168676146519780475390875)
  ·
    refine ⟨213253014219779670713086313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142168676146519780475390875 213253014219779670713086313)
    ·
      refine ⟨159939760664834753034814735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213253014219779670713086313 159939760664834753034814735)
      ·
        refine ⟨239909640997252129552222103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159939760664834753034814735 239909640997252129552222103)
        ·
          refine ⟨359864461495878194328333155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239909640997252129552222103 359864461495878194328333155)
          ·
            refine ⟨539796692243817291492499733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359864461495878194328333155 539796692243817291492499733)
            ·
              refine ⟨25302969948928935538710925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 539796692243817291492499733 25302969948928935538710925)
              ·
                refine ⟨9488613730848350827016597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25302969948928935538710925 9488613730848350827016597)
                ·
                  refine ⟨444778768633516445016403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9488613730848350827016597 444778768633516445016403)
                  ·
                    rfl

theorem cell23_7795832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 6].length) (baseStart_7795832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795832 prefixEnd_7795832 := by exact prefixLift 7795832
  have htrace : WordTrace (prefixWord ++ tailWord_7795832) baseStart_7795832 baseEnd_7795832 := by
    simpa [prefixWord, tailWord_7795832, baseEnd_7795832] using wordTrace_append hprefix tailTrace_7795832
  have hstable : (prefixWord ++ tailWord_7795832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795832).length < 2 ^ (prefixWord ++ tailWord_7795832).sum := by decide
  have hdescent : baseEnd_7795832 < baseStart_7795832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795866 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 6]
def baseStart_7795866 : Nat := 118140960795 + 7795866 * 2 ^ 59
def prefixEnd_7795866 : Nat := 4983230072969 + 3 ^ 40 * 7795866 * 2
def baseEnd_7795866 : Nat := 444780708449322319124719

theorem tailTrace_7795866 : CollatzResearch.WordTrace tailWord_7795866 prefixEnd_7795866 444780708449322319124719 := by
  unfold tailWord_7795866
  simp only [CollatzResearch.WordTrace]
  refine ⟨71084648093729096189379863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189559061583277589838346301 71084648093729096189379863)
  ·
    refine ⟨106626972140593644284069795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71084648093729096189379863 106626972140593644284069795)
    ·
      refine ⟨159940458210890466426104693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106626972140593644284069795 159940458210890466426104693)
      ·
        refine ⟨14994417957270981227447315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159940458210890466426104693 14994417957270981227447315)
        ·
          refine ⟨22491626935906471841170973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14994417957270981227447315 22491626935906471841170973)
          ·
            refine ⟨8434360100964926940439115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22491626935906471841170973 8434360100964926940439115)
            ·
              refine ⟨12651540151447390410658673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434360100964926940439115 12651540151447390410658673)
              ·
                refine ⟨9488655113585542807994005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12651540151447390410658673 9488655113585542807994005)
                ·
                  refine ⟨444780708449322319124719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9488655113585542807994005 444780708449322319124719)
                  ·
                    rfl

theorem cell23_7795866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_7795866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795866 prefixEnd_7795866 := by exact prefixLift 7795866
  have htrace : WordTrace (prefixWord ++ tailWord_7795866) baseStart_7795866 baseEnd_7795866 := by
    simpa [prefixWord, tailWord_7795866, baseEnd_7795866] using wordTrace_append hprefix tailTrace_7795866
  have hstable : (prefixWord ++ tailWord_7795866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795866).length < 2 ^ (prefixWord ++ tailWord_7795866).sum := by decide
  have hdescent : baseEnd_7795866 < baseStart_7795866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795876 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_7795876 : Nat := 118140960795 + 7795876 * 2 ^ 59
def prefixEnd_7795876 : Nat := 4983230072969 + 3 ^ 40 * 7795876 * 2
def baseEnd_7795876 : Nat := 4003031510850445832997425

theorem tailTrace_7795876 : CollatzResearch.WordTrace tailWord_7795876 prefixEnd_7795876 4003031510850445832997425 := by
  unfold tailWord_7795876
  simp only [CollatzResearch.WordTrace]
  refine ⟨142169478552440078232691741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189559304736586770976922321 142169478552440078232691741)
  ·
    refine ⟨53313554457165029337259403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142169478552440078232691741 53313554457165029337259403)
    ·
      refine ⟨79970331685747544005889105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53313554457165029337259403 79970331685747544005889105)
      ·
        refine ⟨59977748764310658004416829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79970331685747544005889105 59977748764310658004416829)
        ·
          refine ⟨22491655786616496751656311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59977748764310658004416829 22491655786616496751656311)
          ·
            refine ⟨33737483679924745127484467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22491655786616496751656311 33737483679924745127484467)
            ·
              refine ⟨50606225519887117691226701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33737483679924745127484467 50606225519887117691226701)
              ·
                refine ⟨18977334569957669134210013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50606225519887117691226701 18977334569957669134210013)
                ·
                  refine ⟨7116500463734125925328755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18977334569957669134210013 7116500463734125925328755)
                  ·
                    refine ⟨10674750695601188887993133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7116500463734125925328755 10674750695601188887993133)
                    ·
                      refine ⟨4003031510850445832997425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10674750695601188887993133 4003031510850445832997425)
                      ·
                        rfl

theorem cell23_7795876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_7795876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795876 prefixEnd_7795876 := by exact prefixLift 7795876
  have htrace : WordTrace (prefixWord ++ tailWord_7795876) baseStart_7795876 baseEnd_7795876 := by
    simpa [prefixWord, tailWord_7795876, baseEnd_7795876] using wordTrace_append hprefix tailTrace_7795876
  have hstable : (prefixWord ++ tailWord_7795876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795876).length < 2 ^ (prefixWord ++ tailWord_7795876).sum := by decide
  have hdescent : baseEnd_7795876 < baseStart_7795876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795943 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 2, 4]
def baseStart_7795943 : Nat := 118140960795 + 7795943 * 2 ^ 59
def prefixEnd_7795943 : Nat := 4983230072969 + 3 ^ 40 * 7795943 * 2
def baseEnd_7795943 : Nat := 1334355304684765690286539

theorem tailTrace_7795943 : CollatzResearch.WordTrace tailWord_7795943 prefixEnd_7795943 1334355304684765690286539 := by
  unfold tailWord_7795943
  simp only [CollatzResearch.WordTrace]
  refine ⟨284341400795637426908072483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189560933863758284605381655 284341400795637426908072483)
  ·
    refine ⟨426512101193456140362108725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284341400795637426908072483 426512101193456140362108725)
    ·
      refine ⟨39985509486886513158947693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426512101193456140362108725 39985509486886513158947693)
      ·
        refine ⟨14994566057582442434605385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39985509486886513158947693 14994566057582442434605385)
        ·
          refine ⟨11245924543186831825954039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14994566057582442434605385 11245924543186831825954039)
          ·
            refine ⟨16868886814780247738931059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11245924543186831825954039 16868886814780247738931059)
            ·
              refine ⟨25303330222170371608396589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16868886814780247738931059 25303330222170371608396589)
              ·
                refine ⟨9488748833313889353148721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25303330222170371608396589 9488748833313889353148721)
                ·
                  refine ⟨7116561624985417014861541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9488748833313889353148721 7116561624985417014861541)
                  ·
                    refine ⟨1334355304684765690286539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7116561624985417014861541 1334355304684765690286539)
                    ·
                      rfl

theorem cell23_7795943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_7795943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795943 prefixEnd_7795943 := by exact prefixLift 7795943
  have htrace : WordTrace (prefixWord ++ tailWord_7795943) baseStart_7795943 baseEnd_7795943 := by
    simpa [prefixWord, tailWord_7795943, baseEnd_7795943] using wordTrace_append hprefix tailTrace_7795943
  have hstable : (prefixWord ++ tailWord_7795943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795943).length < 2 ^ (prefixWord ++ tailWord_7795943).sum := by decide
  have hdescent : baseEnd_7795943 < baseStart_7795943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795959 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 7, 2]
def baseStart_7795959 : Nat := 118140960795 + 7795959 * 2 ^ 59
def prefixEnd_7795959 : Nat := 4983230072969 + 3 ^ 40 * 7795959 * 2
def baseEnd_7795959 : Nat := 4003074129744769008259543

theorem tailTrace_7795959 : CollatzResearch.WordTrace tailWord_7795959 prefixEnd_7795959 4003074129744769008259543 := by
  unfold tailWord_7795959
  simp only [CollatzResearch.WordTrace]
  refine ⟨284341984363579461640654931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189561322909052974427103287 284341984363579461640654931)
  ·
    refine ⟨426512976545369192460982397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284341984363579461640654931 426512976545369192460982397)
    ·
      refine ⟨159942366204513447172868399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426512976545369192460982397 159942366204513447172868399)
      ·
        refine ⟨239913549306770170759302599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159942366204513447172868399 239913549306770170759302599)
        ·
          refine ⟨359870323960155256138953899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239913549306770170759302599 359870323960155256138953899)
          ·
            refine ⟨539805485940232884208430849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359870323960155256138953899 539805485940232884208430849)
            ·
              refine ⟨404854114455174663156323137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539805485940232884208430849 404854114455174663156323137)
              ·
                refine ⟨303640585841380997367242353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404854114455174663156323137 303640585841380997367242353)
                ·
                  refine ⟨227730439381035748025431765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303640585841380997367242353 227730439381035748025431765)
                  ·
                    refine ⟨5337432172993025344346057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227730439381035748025431765 5337432172993025344346057)
                    ·
                      refine ⟨4003074129744769008259543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337432172993025344346057 4003074129744769008259543)
                      ·
                        rfl

theorem cell23_7795959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_7795959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795959 prefixEnd_7795959 := by exact prefixLift 7795959
  have htrace : WordTrace (prefixWord ++ tailWord_7795959) baseStart_7795959 baseEnd_7795959 := by
    simpa [prefixWord, tailWord_7795959, baseEnd_7795959] using wordTrace_append hprefix tailTrace_7795959
  have hstable : (prefixWord ++ tailWord_7795959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795959).length < 2 ^ (prefixWord ++ tailWord_7795959).sum := by decide
  have hdescent : baseEnd_7795959 < baseStart_7795959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795966 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7795966 : Nat := 118140960795 + 7795966 * 2 ^ 59
def prefixEnd_7795966 : Nat := 4983230072969 + 3 ^ 40 * 7795966 * 2
def baseEnd_7795966 : Nat := 4003077724109350480872011

theorem tailTrace_7795966 : CollatzResearch.WordTrace tailWord_7795966 prefixEnd_7795966 4003077724109350480872011 := by
  unfold tailWord_7795966
  simp only [CollatzResearch.WordTrace]
  refine ⟨35542779959319262729519969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189561493116369401224106501 35542779959319262729519969)
  ·
    refine ⟨26657084969489447047139977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35542779959319262729519969 26657084969489447047139977)
    ·
      refine ⟨19992813727117085285354983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26657084969489447047139977 19992813727117085285354983)
      ·
        refine ⟨29989220590675627928032475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19992813727117085285354983 29989220590675627928032475)
        ·
          refine ⟨44983830886013441892048713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29989220590675627928032475 44983830886013441892048713)
          ·
            refine ⟨33737873164510081419036535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44983830886013441892048713 33737873164510081419036535)
            ·
              refine ⟨50606809746765122128554803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33737873164510081419036535 50606809746765122128554803)
              ·
                refine ⟨75910214620147683192832205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50606809746765122128554803 75910214620147683192832205)
                ·
                  refine ⟨28466330482555381197312077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75910214620147683192832205 28466330482555381197312077)
                  ·
                    refine ⟨10674873930958267948992029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28466330482555381197312077 10674873930958267948992029)
                    ·
                      refine ⟨4003077724109350480872011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10674873930958267948992029 4003077724109350480872011)
                      ·
                        rfl

theorem cell23_7795966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7795966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795966 prefixEnd_7795966 := by exact prefixLift 7795966
  have htrace : WordTrace (prefixWord ++ tailWord_7795966) baseStart_7795966 baseEnd_7795966 := by
    simpa [prefixWord, tailWord_7795966, baseEnd_7795966] using wordTrace_append hprefix tailTrace_7795966
  have hstable : (prefixWord ++ tailWord_7795966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795966).length < 2 ^ (prefixWord ++ tailWord_7795966).sum := by decide
  have hdescent : baseEnd_7795966 < baseStart_7795966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7795970 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_7795970 : Nat := 118140960795 + 7795970 * 2 ^ 59
def prefixEnd_7795970 : Nat := 4983230072969 + 3 ^ 40 * 7795970 * 2
def baseEnd_7795970 : Nat := 4003079778031968465221993

theorem tailTrace_7795970 : CollatzResearch.WordTrace tailWord_7795970 prefixEnd_7795970 4003079778031968465221993 := by
  unfold tailWord_7795970
  simp only [CollatzResearch.WordTrace]
  refine ⟨71085596391634902629826341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189561590377693073679536909 71085596391634902629826341)
  ·
    refine ⟨13328549323431544243092439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71085596391634902629826341 13328549323431544243092439)
    ·
      refine ⟨19992823985147316364638659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13328549323431544243092439 19992823985147316364638659)
      ·
        refine ⟨29989235977720974546957989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19992823985147316364638659 29989235977720974546957989)
        ·
          refine ⟨5622981745822682727554623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29989235977720974546957989 5622981745822682727554623)
          ·
            refine ⟨8434472618734024091331935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622981745822682727554623 8434472618734024091331935)
            ·
              refine ⟨12651708928101036136997903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434472618734024091331935 12651708928101036136997903)
              ·
                refine ⟨18977563392151554205496855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12651708928101036136997903 18977563392151554205496855)
                ·
                  refine ⟨28466345088227331308245283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18977563392151554205496855 28466345088227331308245283)
                  ·
                    refine ⟨42699517632340996962367925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28466345088227331308245283 42699517632340996962367925)
                    ·
                      refine ⟨4003079778031968465221993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42699517632340996962367925 4003079778031968465221993)
                      ·
                        rfl

theorem cell23_7795970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_7795970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7795970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7795970 prefixEnd_7795970 := by exact prefixLift 7795970
  have htrace : WordTrace (prefixWord ++ tailWord_7795970) baseStart_7795970 baseEnd_7795970 := by
    simpa [prefixWord, tailWord_7795970, baseEnd_7795970] using wordTrace_append hprefix tailTrace_7795970
  have hstable : (prefixWord ++ tailWord_7795970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7795970).length < 2 ^ (prefixWord ++ tailWord_7795970).sum := by decide
  have hdescent : baseEnd_7795970 < baseStart_7795970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7795970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796046 : List Nat := [4, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_7796046 : Nat := 118140960795 + 7796046 * 2 ^ 59
def prefixEnd_7796046 : Nat := 4983230072969 + 3 ^ 40 * 7796046 * 2
def baseEnd_7796046 : Nat := 444790978062412240874627

theorem tailTrace_7796046 : CollatzResearch.WordTrace tailWord_7796046 prefixEnd_7796046 444790978062412240874627 := by
  unfold tailWord_7796046
  simp only [CollatzResearch.WordTrace]
  refine ⟨35543144689283034437383999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189563438342842850332714661 35543144689283034437383999)
  ·
    refine ⟨53314717033924551656075999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35543144689283034437383999 53314717033924551656075999)
    ·
      refine ⟨79972075550886827484113999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53314717033924551656075999 79972075550886827484113999)
      ·
        refine ⟨119958113326330241226170999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79972075550886827484113999 119958113326330241226170999)
        ·
          refine ⟨179937169989495361839256499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119958113326330241226170999 179937169989495361839256499)
          ·
            refine ⟨269905754984243042758884749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179937169989495361839256499 269905754984243042758884749)
            ·
              refine ⟨101214658119091141034581781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269905754984243042758884749 101214658119091141034581781)
              ·
                refine ⟨4744437099332397235996021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101214658119091141034581781 4744437099332397235996021)
                ·
                  refine ⟨444790978062412240874627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4744437099332397235996021 444790978062412240874627)
                  ·
                    rfl

theorem cell23_7796046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_7796046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796046 prefixEnd_7796046 := by exact prefixLift 7796046
  have htrace : WordTrace (prefixWord ++ tailWord_7796046) baseStart_7796046 baseEnd_7796046 := by
    simpa [prefixWord, tailWord_7796046, baseEnd_7796046] using wordTrace_append hprefix tailTrace_7796046
  have hstable : (prefixWord ++ tailWord_7796046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796046).length < 2 ^ (prefixWord ++ tailWord_7796046).sum := by decide
  have hdescent : baseEnd_7796046 < baseStart_7796046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796079 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_7796079 : Nat := 118140960795 + 7796079 * 2 ^ 59
def prefixEnd_7796079 : Nat := 4983230072969 + 3 ^ 40 * 7796079 * 2
def baseEnd_7796079 : Nat := 4003135747423308538758991

theorem tailTrace_7796079 : CollatzResearch.WordTrace tailWord_7796079 prefixEnd_7796079 4003135747423308538758991 := by
  unfold tailWord_7796079
  simp only [CollatzResearch.WordTrace]
  refine ⟨284346361123144722135023291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189564240748763148090015527 284346361123144722135023291)
  ·
    refine ⟨426519541684717083202534937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284346361123144722135023291 426519541684717083202534937)
    ·
      refine ⟨319889656263537812401901203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426519541684717083202534937 319889656263537812401901203)
      ·
        refine ⟨479834484395306718602851805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319889656263537812401901203 479834484395306718602851805)
        ·
          refine ⟨179937931648240019476069427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479834484395306718602851805 179937931648240019476069427)
          ·
            refine ⟨269906897472360029214104141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179937931648240019476069427 269906897472360029214104141)
            ·
              refine ⟨101215086552135010955289053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269906897472360029214104141 101215086552135010955289053)
              ·
                refine ⟨37955657457050629108233395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101215086552135010955289053 37955657457050629108233395)
                ·
                  refine ⟨56933486185575943662350093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37955657457050629108233395 56933486185575943662350093)
                  ·
                    refine ⟨21350057319590978873381285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56933486185575943662350093 21350057319590978873381285)
                    ·
                      refine ⟨4003135747423308538758991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21350057319590978873381285 4003135747423308538758991)
                      ·
                        rfl

theorem cell23_7796079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_7796079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796079 prefixEnd_7796079 := by exact prefixLift 7796079
  have htrace : WordTrace (prefixWord ++ tailWord_7796079) baseStart_7796079 baseEnd_7796079 := by
    simpa [prefixWord, tailWord_7796079, baseEnd_7796079] using wordTrace_append hprefix tailTrace_7796079
  have hstable : (prefixWord ++ tailWord_7796079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796079).length < 2 ^ (prefixWord ++ tailWord_7796079).sum := by decide
  have hdescent : baseEnd_7796079 < baseStart_7796079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796096 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 4, 4, 2]
def baseStart_7796096 : Nat := 118140960795 + 7796096 * 2 ^ 59
def prefixEnd_7796096 : Nat := 4983230072969 + 3 ^ 40 * 7796096 * 2
def baseEnd_7796096 : Nat := 4003144476594434972246413

theorem tailTrace_7796096 : CollatzResearch.WordTrace tailWord_7796096 prefixEnd_7796096 4003144476594434972246413 := by
  unfold tailWord_7796096
  simp only [CollatzResearch.WordTrace]
  refine ⟨142173490582041567019196071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189564654109388756025594761 142173490582041567019196071)
  ·
    refine ⟨213260235873062350528794107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142173490582041567019196071 213260235873062350528794107)
    ·
      refine ⟨319890353809593525793191161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213260235873062350528794107 319890353809593525793191161)
      ·
        refine ⟨239917765357195144344893371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319890353809593525793191161 239917765357195144344893371)
        ·
          refine ⟨359876648035792716517340057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239917765357195144344893371 359876648035792716517340057)
          ·
            refine ⟨269907486026844537388005043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359876648035792716517340057 269907486026844537388005043)
            ·
              refine ⟨404861229040266806082007565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269907486026844537388005043 404861229040266806082007565)
              ·
                refine ⟨151822960890100052280752837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404861229040266806082007565 151822960890100052280752837)
                ·
                  refine ⟨28466805166893759802641157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151822960890100052280752837 28466805166893759802641157)
                  ·
                    refine ⟨5337525968792579962995217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28466805166893759802641157 5337525968792579962995217)
                    ·
                      refine ⟨4003144476594434972246413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337525968792579962995217 4003144476594434972246413)
                      ·
                        rfl

theorem cell23_7796096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_7796096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796096 prefixEnd_7796096 := by exact prefixLift 7796096
  have htrace : WordTrace (prefixWord ++ tailWord_7796096) baseStart_7796096 baseEnd_7796096 := by
    simpa [prefixWord, tailWord_7796096, baseEnd_7796096] using wordTrace_append hprefix tailTrace_7796096
  have hstable : (prefixWord ++ tailWord_7796096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796096).length < 2 ^ (prefixWord ++ tailWord_7796096).sum := by decide
  have hdescent : baseEnd_7796096 < baseStart_7796096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796153 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 6]
def baseStart_7796153 : Nat := 118140960795 + 7796153 * 2 ^ 59
def prefixEnd_7796153 : Nat := 4983230072969 + 3 ^ 40 * 7796153 * 2
def baseEnd_7796153 : Nat := 444797082776860138803739

theorem tailTrace_7796153 : CollatzResearch.WordTrace tailWord_7796153 prefixEnd_7796153 444797082776860138803739 := by
  unfold tailWord_7796153
  simp only [CollatzResearch.WordTrace]
  refine ⟨284349060124876632773217113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189566040083251088515478075 284349060124876632773217113)
  ·
    refine ⟨213261795093657474579912835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284349060124876632773217113 213261795093657474579912835)
    ·
      refine ⟨319892692640486211869869253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213261795093657474579912835 319892692640486211869869253)
      ·
        refine ⟨59979879870091164725600485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319892692640486211869869253 59979879870091164725600485)
        ·
          refine ⟨11246227475642093386050091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59979879870091164725600485 11246227475642093386050091)
          ·
            refine ⟨16869341213463140079075137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11246227475642093386050091 16869341213463140079075137)
            ·
              refine ⟨12652005910097355059306353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16869341213463140079075137 12652005910097355059306353)
              ·
                refine ⟨9489004432573016294479765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12652005910097355059306353 9489004432573016294479765)
                ·
                  refine ⟨444797082776860138803739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9489004432573016294479765 444797082776860138803739)
                  ·
                    rfl

theorem cell23_7796153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 6].length) (baseStart_7796153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796153 prefixEnd_7796153 := by exact prefixLift 7796153
  have htrace : WordTrace (prefixWord ++ tailWord_7796153) baseStart_7796153 baseEnd_7796153 := by
    simpa [prefixWord, tailWord_7796153, baseEnd_7796153] using wordTrace_append hprefix tailTrace_7796153
  have hstable : (prefixWord ++ tailWord_7796153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796153).length < 2 ^ (prefixWord ++ tailWord_7796153).sum := by decide
  have hdescent : baseEnd_7796153 < baseStart_7796153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796159 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_7796159 : Nat := 118140960795 + 7796159 * 2 ^ 59
def prefixEnd_7796159 : Nat := 4983230072969 + 3 ^ 40 * 7796159 * 2
def baseEnd_7796159 : Nat := 4003176825875668225758623

theorem tailTrace_7796159 : CollatzResearch.WordTrace tailWord_7796159 prefixEnd_7796159 4003176825875668225758623 := by
  unfold tailWord_7796159
  simp only [CollatzResearch.WordTrace]
  refine ⟨284349278962854895797935531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189566185975236597198623687 284349278962854895797935531)
  ·
    refine ⟨426523918444282343696903297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284349278962854895797935531 426523918444282343696903297)
    ·
      refine ⟨319892938833211757772677473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426523918444282343696903297 319892938833211757772677473)
      ·
        refine ⟨239919704124908818329508105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319892938833211757772677473 239919704124908818329508105)
        ·
          refine ⟨179939778093681613747131079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239919704124908818329508105 179939778093681613747131079)
          ·
            refine ⟨269909667140522420620696619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179939778093681613747131079 269909667140522420620696619)
            ·
              refine ⟨404864500710783630931044929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269909667140522420620696619 404864500710783630931044929)
              ·
                refine ⟨303648375533087723198283697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404864500710783630931044929 303648375533087723198283697)
                ·
                  refine ⟨227736281649815792398712773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303648375533087723198283697 227736281649815792398712773)
                  ·
                    refine ⟨42700552809340461074758645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227736281649815792398712773 42700552809340461074758645)
                    ·
                      refine ⟨4003176825875668225758623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42700552809340461074758645 4003176825875668225758623)
                      ·
                        rfl

theorem cell23_7796159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_7796159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796159 prefixEnd_7796159 := by exact prefixLift 7796159
  have htrace : WordTrace (prefixWord ++ tailWord_7796159) baseStart_7796159 baseEnd_7796159 := by
    simpa [prefixWord, tailWord_7796159, baseEnd_7796159] using wordTrace_append hprefix tailTrace_7796159
  have hstable : (prefixWord ++ tailWord_7796159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796159).length < 2 ^ (prefixWord ++ tailWord_7796159).sum := by decide
  have hdescent : baseEnd_7796159 < baseStart_7796159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796197 : List Nat := [1, 3, 1, 5, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7796197 : Nat := 118140960795 + 7796197 * 2 ^ 59
def prefixEnd_7796197 : Nat := 4983230072969 + 3 ^ 40 * 7796197 * 2
def baseEnd_7796197 : Nat := 4003196338140539077083449

theorem tailTrace_7796197 : CollatzResearch.WordTrace tailWord_7796197 prefixEnd_7796197 4003196338140539077083449 := by
  unfold tailWord_7796197
  simp only [CollatzResearch.WordTrace]
  refine ⟨284350664936717228287818845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189567109957811485525212563 284350664936717228287818845)
  ·
    refine ⟨106631499351268960607932067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284350664936717228287818845 106631499351268960607932067)
    ·
      refine ⟨159947249026903440911898101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106631499351268960607932067 159947249026903440911898101)
      ·
        refine ⟨14995054596272197585490447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159947249026903440911898101 14995054596272197585490447)
        ·
          refine ⟨22492581894408296378235671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14995054596272197585490447 22492581894408296378235671)
          ·
            refine ⟨33738872841612444567353507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22492581894408296378235671 33738872841612444567353507)
            ·
              refine ⟨50608309262418666851030261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33738872841612444567353507 50608309262418666851030261)
              ·
                refine ⟨4744528993351750017284087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50608309262418666851030261 4744528993351750017284087)
                ·
                  refine ⟨7116793490027625025926131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744528993351750017284087 7116793490027625025926131)
                  ·
                    refine ⟨10675190235041437538889197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7116793490027625025926131 10675190235041437538889197)
                    ·
                      refine ⟨4003196338140539077083449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10675190235041437538889197 4003196338140539077083449)
                      ·
                        rfl

theorem cell23_7796197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7796197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796197 prefixEnd_7796197 := by exact prefixLift 7796197
  have htrace : WordTrace (prefixWord ++ tailWord_7796197) baseStart_7796197 baseEnd_7796197 := by
    simpa [prefixWord, tailWord_7796197, baseEnd_7796197] using wordTrace_append hprefix tailTrace_7796197
  have hstable : (prefixWord ++ tailWord_7796197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796197).length < 2 ^ (prefixWord ++ tailWord_7796197).sum := by decide
  have hdescent : baseEnd_7796197 < baseStart_7796197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796220 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_7796220 : Nat := 118140960795 + 7796220 * 2 ^ 59
def prefixEnd_7796220 : Nat := 4983230072969 + 3 ^ 40 * 7796220 * 2
def baseEnd_7796220 : Nat := 4003208148195592487095843

theorem tailTrace_7796220 : CollatzResearch.WordTrace tailWord_7796220 prefixEnd_7796220 4003208148195592487095843 := by
  unfold tailWord_7796220
  simp only [CollatzResearch.WordTrace]
  refine ⟨142175751907816951607953057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189567669210422602143937409 142175751907816951607953057)
  ·
    refine ⟨106631813930862713705964793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142175751907816951607953057 106631813930862713705964793)
    ·
      refine ⟨79973860448147035279473595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106631813930862713705964793 79973860448147035279473595)
      ·
        refine ⟨119960790672220552919210393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79973860448147035279473595 119960790672220552919210393)
        ·
          refine ⟨89970593004165414689407795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119960790672220552919210393 89970593004165414689407795)
          ·
            refine ⟨134955889506248122034111693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89970593004165414689407795 134955889506248122034111693)
            ·
              refine ⟨50608458564843045762791885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134955889506248122034111693 50608458564843045762791885)
              ·
                refine ⟨18978171961816142161046957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50608458564843045762791885 18978171961816142161046957)
                ·
                  refine ⟨7116814485681053310392609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18978171961816142161046957 7116814485681053310392609)
                  ·
                    refine ⟨5337610864260789982794457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7116814485681053310392609 5337610864260789982794457)
                    ·
                      refine ⟨4003208148195592487095843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337610864260789982794457 4003208148195592487095843)
                      ·
                        rfl

theorem cell23_7796220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_7796220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796220 prefixEnd_7796220 := by exact prefixLift 7796220
  have htrace : WordTrace (prefixWord ++ tailWord_7796220) baseStart_7796220 baseEnd_7796220 := by
    simpa [prefixWord, tailWord_7796220, baseEnd_7796220] using wordTrace_append hprefix tailTrace_7796220
  have hstable : (prefixWord ++ tailWord_7796220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796220).length < 2 ^ (prefixWord ++ tailWord_7796220).sum := by decide
  have hdescent : baseEnd_7796220 < baseStart_7796220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796243 : List Nat := [1, 1, 1, 2, 1, 8, 2, 7]
def baseStart_7796243 : Nat := 118140960795 + 7796243 * 2 ^ 59
def prefixEnd_7796243 : Nat := 4983230072969 + 3 ^ 40 * 7796243 * 2
def baseEnd_7796243 : Nat := 148267405861135033226231

theorem tailTrace_7796243 : CollatzResearch.WordTrace tailWord_7796243 prefixEnd_7796243 148267405861135033226231 := by
  unfold tailWord_7796243
  simp only [CollatzResearch.WordTrace]
  refine ⟨284352342694550578143993383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189568228463033718762662255 284352342694550578143993383)
  ·
    refine ⟨426528514041825867215990075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284352342694550578143993383 426528514041825867215990075)
    ·
      refine ⟨639792771062738800823985113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426528514041825867215990075 639792771062738800823985113)
      ·
        refine ⟨479844578297054100617988835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639792771062738800823985113 479844578297054100617988835)
        ·
          refine ⟨719766867445581150926983253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479844578297054100617988835 719766867445581150926983253)
          ·
            refine ⟨8434767977877904112425585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 719766867445581150926983253 8434767977877904112425585)
            ·
              refine ⟨6326075983408428084319189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8434767977877904112425585 6326075983408428084319189)
              ·
                refine ⟨148267405861135033226231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6326075983408428084319189 148267405861135033226231)
                ·
                  rfl

theorem cell23_7796243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 7].length) (baseStart_7796243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796243 prefixEnd_7796243 := by exact prefixLift 7796243
  have htrace : WordTrace (prefixWord ++ tailWord_7796243) baseStart_7796243 baseEnd_7796243 := by
    simpa [prefixWord, tailWord_7796243, baseEnd_7796243] using wordTrace_append hprefix tailTrace_7796243
  have hstable : (prefixWord ++ tailWord_7796243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796243).length < 2 ^ (prefixWord ++ tailWord_7796243).sum := by decide
  have hdescent : baseEnd_7796243 < baseStart_7796243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796253 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_7796253 : Nat := 118140960795 + 7796253 * 2 ^ 59
def prefixEnd_7796253 : Nat := 4983230072969 + 3 ^ 40 * 7796253 * 2
def baseEnd_7796253 : Nat := 4003225093057190857983191

theorem tailTrace_7796253 : CollatzResearch.WordTrace tailWord_7796253 prefixEnd_7796253 4003225093057190857983191 := by
  unfold tailWord_7796253
  simp only [CollatzResearch.WordTrace]
  refine ⟨284352707424514349851857413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189568471616342899901238275 284352707424514349851857413)
  ·
    refine ⟨53316132642096440597223265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284352707424514349851857413 53316132642096440597223265)
    ·
      refine ⟨39987099481572330447917449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53316132642096440597223265 39987099481572330447917449)
      ·
        refine ⟨29990324611179247835938087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39987099481572330447917449 29990324611179247835938087)
        ·
          refine ⟨44985486916768871753907131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29990324611179247835938087 44985486916768871753907131)
          ·
            refine ⟨67478230375153307630860697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44985486916768871753907131 67478230375153307630860697)
            ·
              refine ⟨50608672781364980723145523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67478230375153307630860697 50608672781364980723145523)
              ·
                refine ⟨75913009172047471084718285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50608672781364980723145523 75913009172047471084718285)
                ·
                  refine ⟨28467378439517801656769357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75913009172047471084718285 28467378439517801656769357)
                  ·
                    refine ⟨10675266914819175621288509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28467378439517801656769357 10675266914819175621288509)
                    ·
                      refine ⟨4003225093057190857983191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10675266914819175621288509 4003225093057190857983191)
                      ·
                        rfl

theorem cell23_7796253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_7796253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796253 prefixEnd_7796253 := by exact prefixLift 7796253
  have htrace : WordTrace (prefixWord ++ tailWord_7796253) baseStart_7796253 baseEnd_7796253 := by
    simpa [prefixWord, tailWord_7796253, baseEnd_7796253] using wordTrace_append hprefix tailTrace_7796253
  have hstable : (prefixWord ++ tailWord_7796253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796253).length < 2 ^ (prefixWord ++ tailWord_7796253).sum := by decide
  have hdescent : baseEnd_7796253 < baseStart_7796253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796287 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 2, 1, 3]
def baseStart_7796287 : Nat := 118140960795 + 7796287 * 2 ^ 59
def prefixEnd_7796287 : Nat := 4983230072969 + 3 ^ 40 * 7796287 * 2
def baseEnd_7796287 : Nat := 4003242551399443724958035

theorem tailTrace_7796287 : CollatzResearch.WordTrace tailWord_7796287 prefixEnd_7796287 4003242551399443724958035 := by
  unfold tailWord_7796287
  simp only [CollatzResearch.WordTrace]
  refine ⟨284353947506391173658595115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189569298337594115772396743 284353947506391173658595115)
  ·
    refine ⟨426530921259586760487892673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284353947506391173658595115 426530921259586760487892673)
    ·
      refine ⟨319898190944690070365919505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426530921259586760487892673 319898190944690070365919505)
      ·
        refine ⟨239923643208517552774439629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319898190944690070365919505 239923643208517552774439629)
        ·
          refine ⟨89971366203194082290414861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239923643208517552774439629 89971366203194082290414861)
          ·
            refine ⟨33739262326197780858905573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89971366203194082290414861 33739262326197780858905573)
            ·
              refine ⟨6326111686162083911044795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33739262326197780858905573 6326111686162083911044795)
              ·
                refine ⟨9489167529243125866567193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326111686162083911044795 9489167529243125866567193)
                ·
                  refine ⟨7116875646932344399925395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9489167529243125866567193 7116875646932344399925395)
                  ·
                    refine ⟨10675313470398516599888093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7116875646932344399925395 10675313470398516599888093)
                    ·
                      refine ⟨4003242551399443724958035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10675313470398516599888093 4003242551399443724958035)
                      ·
                        rfl

theorem cell23_7796287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_7796287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796287 prefixEnd_7796287 := by exact prefixLift 7796287
  have htrace : WordTrace (prefixWord ++ tailWord_7796287) baseStart_7796287 baseEnd_7796287 := by
    simpa [prefixWord, tailWord_7796287, baseEnd_7796287] using wordTrace_append hprefix tailTrace_7796287
  have hstable : (prefixWord ++ tailWord_7796287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796287).length < 2 ^ (prefixWord ++ tailWord_7796287).sum := by decide
  have hdescent : baseEnd_7796287 < baseStart_7796287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796327 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_7796327 : Nat := 118140960795 + 7796327 * 2 ^ 59
def prefixEnd_7796327 : Nat := 4983230072969 + 3 ^ 40 * 7796327 * 2
def baseEnd_7796327 : Nat := 4003263090625623568457851

theorem tailTrace_7796327 : CollatzResearch.WordTrace tailWord_7796327 prefixEnd_7796327 4003263090625623568457851 := by
  unfold tailWord_7796327
  simp only [CollatzResearch.WordTrace]
  refine ⟨284355406426246260490051235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189570270950830840326700823 284355406426246260490051235)
  ·
    refine ⟨426533109639369390735076853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284355406426246260490051235 426533109639369390735076853)
    ·
      refine ⟨39987479028690880381413455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426533109639369390735076853 39987479028690880381413455)
      ·
        refine ⟨59981218543036320572120183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39987479028690880381413455 59981218543036320572120183)
        ·
          refine ⟨89971827814554480858180275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59981218543036320572120183 89971827814554480858180275)
          ·
            refine ⟨134957741721831721287270413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89971827814554480858180275 134957741721831721287270413)
            ·
              refine ⟨50609153145686895482726405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134957741721831721287270413 50609153145686895482726405)
              ·
                refine ⟨9489216214816292903011201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50609153145686895482726405 9489216214816292903011201)
                ·
                  refine ⟨7116912161112219677258401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9489216214816292903011201 7116912161112219677258401)
                  ·
                    refine ⟨5337684120834164757943801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7116912161112219677258401 5337684120834164757943801)
                    ·
                      refine ⟨4003263090625623568457851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337684120834164757943801 4003263090625623568457851)
                      ·
                        rfl

theorem cell23_7796327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_7796327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796327 prefixEnd_7796327 := by exact prefixLift 7796327
  have htrace : WordTrace (prefixWord ++ tailWord_7796327) baseStart_7796327 baseEnd_7796327 := by
    simpa [prefixWord, tailWord_7796327, baseEnd_7796327] using wordTrace_append hprefix tailTrace_7796327
  have hstable : (prefixWord ++ tailWord_7796327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796327).length < 2 ^ (prefixWord ++ tailWord_7796327).sum := by decide
  have hdescent : baseEnd_7796327 < baseStart_7796327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796400 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 2, 4, 2]
def baseStart_7796400 : Nat := 118140960795 + 7796400 * 2 ^ 59
def prefixEnd_7796400 : Nat := 4983230072969 + 3 ^ 40 * 7796400 * 2
def baseEnd_7796400 : Nat := 4003300574713401782845015

theorem tailTrace_7796400 : CollatzResearch.WordTrace tailWord_7796400 prefixEnd_7796400 4003300574713401782845015 := by
  unfold tailWord_7796400
  simp only [CollatzResearch.WordTrace]
  refine ⟨142179034477490896978729327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189572045969987862638305769 142179034477490896978729327)
  ·
    refine ⟨213268551716236345468093991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142179034477490896978729327 213268551716236345468093991)
    ·
      refine ⟨319902827574354518202140987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213268551716236345468093991 319902827574354518202140987)
      ·
        refine ⟨479854241361531777303211481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319902827574354518202140987 479854241361531777303211481)
        ·
          refine ⟨359890681021148832977408611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479854241361531777303211481 359890681021148832977408611)
          ·
            refine ⟨539836021531723249466112917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359890681021148832977408611 539836021531723249466112917)
            ·
              refine ⟨25304813509299527318724043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 539836021531723249466112917 25304813509299527318724043)
              ·
                refine ⟨37957220263949290978086065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25304813509299527318724043 37957220263949290978086065)
                ·
                  refine ⟨28467915197961968233564549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37957220263949290978086065 28467915197961968233564549)
                  ·
                    refine ⟨5337734099617869043793353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28467915197961968233564549 5337734099617869043793353)
                    ·
                      refine ⟨4003300574713401782845015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337734099617869043793353 4003300574713401782845015)
                      ·
                        rfl

theorem cell23_7796400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 4, 2].length) (baseStart_7796400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796400 prefixEnd_7796400 := by exact prefixLift 7796400
  have htrace : WordTrace (prefixWord ++ tailWord_7796400) baseStart_7796400 baseEnd_7796400 := by
    simpa [prefixWord, tailWord_7796400, baseEnd_7796400] using wordTrace_append hprefix tailTrace_7796400
  have hstable : (prefixWord ++ tailWord_7796400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796400).length < 2 ^ (prefixWord ++ tailWord_7796400).sum := by decide
  have hdescent : baseEnd_7796400 < baseStart_7796400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796403 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 3]
def baseStart_7796403 : Nat := 118140960795 + 7796403 * 2 ^ 59
def prefixEnd_7796403 : Nat := 4983230072969 + 3 ^ 40 * 7796403 * 2
def baseEnd_7796403 : Nat := 4003302115155365271107501

theorem tailTrace_7796403 : CollatzResearch.WordTrace tailWord_7796403 prefixEnd_7796403 4003302115155365271107501 := by
  unfold tailWord_7796403
  simp only [CollatzResearch.WordTrace]
  refine ⟨284358178373970925469817863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189572118915980616979878575 284358178373970925469817863)
  ·
    refine ⟨426537267560956388204726795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284358178373970925469817863 426537267560956388204726795)
    ·
      refine ⟨639805901341434582307090193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426537267560956388204726795 639805901341434582307090193)
      ·
        refine ⟨479854426006075936730317645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639805901341434582307090193 479854426006075936730317645)
        ·
          refine ⟨179945409752278476273869117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479854426006075936730317645 179945409752278476273869117)
          ·
            refine ⟨67479528657104428602700919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179945409752278476273869117 67479528657104428602700919)
            ·
              refine ⟨101219292985656642904051379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67479528657104428602700919 101219292985656642904051379)
              ·
                refine ⟨151828939478484964356077069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101219292985656642904051379 151828939478484964356077069)
                ·
                  refine ⟨56935852304431861633528901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151828939478484964356077069 56935852304431861633528901)
                  ·
                    refine ⟨10675472307080974056286669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56935852304431861633528901 10675472307080974056286669)
                    ·
                      refine ⟨4003302115155365271107501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10675472307080974056286669 4003302115155365271107501)
                      ·
                        rfl

theorem cell23_7796403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_7796403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796403 prefixEnd_7796403 := by exact prefixLift 7796403
  have htrace : WordTrace (prefixWord ++ tailWord_7796403) baseStart_7796403 baseEnd_7796403 := by
    simpa [prefixWord, tailWord_7796403, baseEnd_7796403] using wordTrace_append hprefix tailTrace_7796403
  have hstable : (prefixWord ++ tailWord_7796403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796403).length < 2 ^ (prefixWord ++ tailWord_7796403).sum := by decide
  have hdescent : baseEnd_7796403 < baseStart_7796403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796410 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_7796410 : Nat := 118140960795 + 7796410 * 2 ^ 59
def prefixEnd_7796410 : Nat := 4983230072969 + 3 ^ 40 * 7796410 * 2
def baseEnd_7796410 : Nat := 1334435236506648914573323

theorem tailTrace_7796410 : CollatzResearch.WordTrace tailWord_7796410 prefixEnd_7796410 1334435236506648914573323 := by
  unfold tailWord_7796410
  simp only [CollatzResearch.WordTrace]
  refine ⟨71089608421236391416330671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189572289123297043776881789 71089608421236391416330671)
  ·
    refine ⟨106634412631854587124496007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71089608421236391416330671 106634412631854587124496007)
    ·
      refine ⟨159951618947781880686744011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106634412631854587124496007 159951618947781880686744011)
      ·
        refine ⟨239927428421672821030116017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159951618947781880686744011 239927428421672821030116017)
        ·
          refine ⟨179945571316254615772587013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239927428421672821030116017 179945571316254615772587013)
          ·
            refine ⟨33739794621797740457360065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179945571316254615772587013 33739794621797740457360065)
            ·
              refine ⟨25304845966348305343020049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33739794621797740457360065 25304845966348305343020049)
              ·
                refine ⟨18978634474761229007265037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25304845966348305343020049 18978634474761229007265037)
                ·
                  refine ⟨7116987928035460877724389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18978634474761229007265037 7116987928035460877724389)
                  ·
                    refine ⟨1334435236506648914573323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7116987928035460877724389 1334435236506648914573323)
                    ·
                      rfl

theorem cell23_7796410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_7796410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796410 prefixEnd_7796410 := by exact prefixLift 7796410
  have htrace : WordTrace (prefixWord ++ tailWord_7796410) baseStart_7796410 baseEnd_7796410 := by
    simpa [prefixWord, tailWord_7796410, baseEnd_7796410] using wordTrace_append hprefix tailTrace_7796410
  have hstable : (prefixWord ++ tailWord_7796410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796410).length < 2 ^ (prefixWord ++ tailWord_7796410).sum := by decide
  have hdescent : baseEnd_7796410 < baseStart_7796410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796413 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7796413 : Nat := 118140960795 + 7796413 * 2 ^ 59
def prefixEnd_7796413 : Nat := 4983230072969 + 3 ^ 40 * 7796413 * 2
def baseEnd_7796413 : Nat := 4003307249961910231982455

theorem tailTrace_7796413 : CollatzResearch.WordTrace tailWord_7796413 prefixEnd_7796413 4003307249961910231982455 := by
  unfold tailWord_7796413
  simp only [CollatzResearch.WordTrace]
  refine ⟨284358543103934697177681893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189572362069289798118454595 284358543103934697177681893)
  ·
    refine ⟨53317226831987755720815355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284358543103934697177681893 53317226831987755720815355)
    ·
      refine ⟨79975840247981633581223033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53317226831987755720815355 79975840247981633581223033)
      ·
        refine ⟨59981880185986225185917275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79975840247981633581223033 59981880185986225185917275)
        ·
          refine ⟨89972820278979337778875913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59981880185986225185917275 89972820278979337778875913)
          ·
            refine ⟨67479615209234503334156935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89972820278979337778875913 67479615209234503334156935)
            ·
              refine ⟨101219422813851755001235403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67479615209234503334156935 101219422813851755001235403)
              ·
                refine ⟨151829134220777632501853105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101219422813851755001235403 151829134220777632501853105)
                ·
                  refine ⟨113871850665583224376389829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151829134220777632501853105 113871850665583224376389829)
                  ·
                    refine ⟨21350971999796854570573093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113871850665583224376389829 21350971999796854570573093)
                    ·
                      refine ⟨4003307249961910231982455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21350971999796854570573093 4003307249961910231982455)
                      ·
                        rfl

theorem cell23_7796413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7796413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796413 prefixEnd_7796413 := by exact prefixLift 7796413
  have htrace : WordTrace (prefixWord ++ tailWord_7796413) baseStart_7796413 baseEnd_7796413 := by
    simpa [prefixWord, tailWord_7796413, baseEnd_7796413] using wordTrace_append hprefix tailTrace_7796413
  have hstable : (prefixWord ++ tailWord_7796413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796413).length < 2 ^ (prefixWord ++ tailWord_7796413).sum := by decide
  have hdescent : baseEnd_7796413 < baseStart_7796413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796418 : List Nat := [3, 5, 1, 2, 1, 2, 1, 3, 5]
def baseStart_7796418 : Nat := 118140960795 + 7796418 * 2 ^ 59
def prefixEnd_7796418 : Nat := 4983230072969 + 3 ^ 40 * 7796418 * 2
def baseEnd_7796418 : Nat := 444812201929464745824437

theorem tailTrace_7796418 : CollatzResearch.WordTrace tailWord_7796418 prefixEnd_7796418 444812201929464745824437 := by
  unfold tailWord_7796418
  simp only [CollatzResearch.WordTrace]
  refine ⟨71089681367229145757903477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189572483645944388687742605 71089681367229145757903477)
  ·
    refine ⟨6664657628177732414803451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71089681367229145757903477 6664657628177732414803451)
    ·
      refine ⟨9996986442266598622205177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664657628177732414803451 9996986442266598622205177)
      ·
        refine ⟨7497739831699948966653883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9996986442266598622205177 7497739831699948966653883)
        ·
          refine ⟨11246609747549923449980825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7497739831699948966653883 11246609747549923449980825)
          ·
            refine ⟨8434957310662442587485619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11246609747549923449980825 8434957310662442587485619)
            ·
              refine ⟨12652435965993663881228429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434957310662442587485619 12652435965993663881228429)
              ·
                refine ⟨4744663487247623955460661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12652435965993663881228429 4744663487247623955460661)
                ·
                  refine ⟨444812201929464745824437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4744663487247623955460661 444812201929464745824437)
                  ·
                    rfl

theorem cell23_7796418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_7796418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796418 prefixEnd_7796418 := by exact prefixLift 7796418
  have htrace : WordTrace (prefixWord ++ tailWord_7796418) baseStart_7796418 baseEnd_7796418 := by
    simpa [prefixWord, tailWord_7796418, baseEnd_7796418] using wordTrace_append hprefix tailTrace_7796418
  have hstable : (prefixWord ++ tailWord_7796418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796418).length < 2 ^ (prefixWord ++ tailWord_7796418).sum := by decide
  have hdescent : baseEnd_7796418 < baseStart_7796418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796420 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_7796420 : Nat := 118140960795 + 7796420 * 2 ^ 59
def prefixEnd_7796420 : Nat := 4983230072969 + 3 ^ 40 * 7796420 * 2
def baseEnd_7796420 : Nat := 4003310844326491704594923

theorem tailTrace_7796420 : CollatzResearch.WordTrace tailWord_7796420 prefixEnd_7796420 4003310844326491704594923 := by
  unfold tailWord_7796420
  simp only [CollatzResearch.WordTrace]
  refine ⟨142179399207454668686593357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189572532276606224915457809 142179399207454668686593357)
  ·
    refine ⟨53317274702795500757472509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142179399207454668686593357 53317274702795500757472509)
    ·
      refine ⟨19993978013548312784052191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53317274702795500757472509 19993978013548312784052191)
      ·
        refine ⟨29990967020322469176078287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19993978013548312784052191 29990967020322469176078287)
        ·
          refine ⟨44986450530483703764117431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29990967020322469176078287 44986450530483703764117431)
          ·
            refine ⟨67479675795725555646176147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44986450530483703764117431 67479675795725555646176147)
            ·
              refine ⟨101219513693588333469264221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67479675795725555646176147 101219513693588333469264221)
              ·
                refine ⟨37957317635095625050974083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101219513693588333469264221 37957317635095625050974083)
                ·
                  refine ⟨56935976452643437576461125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37957317635095625050974083 56935976452643437576461125)
                  ·
                    refine ⟨10675495584870644545586461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56935976452643437576461125 10675495584870644545586461)
                    ·
                      refine ⟨4003310844326491704594923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10675495584870644545586461 4003310844326491704594923)
                      ·
                        rfl

theorem cell23_7796420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_7796420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796420 prefixEnd_7796420 := by exact prefixLift 7796420
  have htrace : WordTrace (prefixWord ++ tailWord_7796420) baseStart_7796420 baseEnd_7796420 := by
    simpa [prefixWord, tailWord_7796420, baseEnd_7796420] using wordTrace_append hprefix tailTrace_7796420
  have hstable : (prefixWord ++ tailWord_7796420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796420).length < 2 ^ (prefixWord ++ tailWord_7796420).sum := by decide
  have hdescent : baseEnd_7796420 < baseStart_7796420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796460 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 3, 5, 2]
def baseStart_7796460 : Nat := 118140960795 + 7796460 * 2 ^ 59
def prefixEnd_7796460 : Nat := 4983230072969 + 3 ^ 40 * 7796460 * 2
def baseEnd_7796460 : Nat := 4003331383552671548094739

theorem tailTrace_7796460 : CollatzResearch.WordTrace tailWord_7796460 prefixEnd_7796460 4003331383552671548094739 := by
  unfold tailWord_7796460
  simp only [CollatzResearch.WordTrace]
  refine ⟨142180128667382212102321417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189573504889842949469761889 142180128667382212102321417)
  ·
    refine ⟨106635096500536659076741063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142180128667382212102321417 106635096500536659076741063)
    ·
      refine ⟨159952644750804988615111595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106635096500536659076741063 159952644750804988615111595)
      ·
        refine ⟨239928967126207482922667393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159952644750804988615111595 239928967126207482922667393)
        ·
          refine ⟨179946725344655612192000545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239928967126207482922667393 179946725344655612192000545)
          ·
            refine ⟨134960044008491709144000409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179946725344655612192000545 134960044008491709144000409)
            ·
              refine ⟨101220033006368781858000307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134960044008491709144000409 101220033006368781858000307)
              ·
                refine ⟨151830049509553172787000461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101220033006368781858000307 151830049509553172787000461)
                ·
                  refine ⟨56936268566082439795125173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151830049509553172787000461 56936268566082439795125173)
                  ·
                    refine ⟨5337775178070228730792985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56936268566082439795125173 5337775178070228730792985)
                    ·
                      refine ⟨4003331383552671548094739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337775178070228730792985 4003331383552671548094739)
                      ·
                        rfl

theorem cell23_7796460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_7796460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796460 prefixEnd_7796460 := by exact prefixLift 7796460
  have htrace : WordTrace (prefixWord ++ tailWord_7796460) baseStart_7796460 baseEnd_7796460 := by
    simpa [prefixWord, tailWord_7796460, baseEnd_7796460] using wordTrace_append hprefix tailTrace_7796460
  have hstable : (prefixWord ++ tailWord_7796460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796460).length < 2 ^ (prefixWord ++ tailWord_7796460).sum := by decide
  have hdescent : baseEnd_7796460 < baseStart_7796460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796483 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 3, 6]
def baseStart_7796483 : Nat := 118140960795 + 7796483 * 2 ^ 59
def prefixEnd_7796483 : Nat := 4983230072969 + 3 ^ 40 * 7796483 * 2
def baseEnd_7796483 : Nat := 1334447731202574986035711

theorem tailTrace_7796483 : CollatzResearch.WordTrace tailWord_7796483 prefixEnd_7796483 1334447731202574986035711 := by
  unfold tailWord_7796483
  simp only [CollatzResearch.WordTrace]
  refine ⟨284361096213681099132730103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189574064142454066088486735 284361096213681099132730103)
  ·
    refine ⟨426541644320521648699095155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284361096213681099132730103 426541644320521648699095155)
    ·
      refine ⟨639812466480782473048642733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426541644320521648699095155 639812466480782473048642733)
      ·
        refine ⟨239929674930293427393241025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639812466480782473048642733 239929674930293427393241025)
        ·
          refine ⟨179947256197720070544930769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239929674930293427393241025 179947256197720070544930769)
          ·
            refine ⟨134960442148290052908698077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179947256197720070544930769 134960442148290052908698077)
            ·
              refine ⟨50610165805608769840761779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134960442148290052908698077 50610165805608769840761779)
              ·
                refine ⟨75915248708413154761142669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50610165805608769840761779 75915248708413154761142669)
                ·
                  refine ⟨28468218265654933035428501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75915248708413154761142669 28468218265654933035428501)
                  ·
                    refine ⟨1334447731202574986035711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28468218265654933035428501 1334447731202574986035711)
                    ·
                      rfl

theorem cell23_7796483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 6].length) (baseStart_7796483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796483 prefixEnd_7796483 := by exact prefixLift 7796483
  have htrace : WordTrace (prefixWord ++ tailWord_7796483) baseStart_7796483 baseEnd_7796483 := by
    simpa [prefixWord, tailWord_7796483, baseEnd_7796483] using wordTrace_append hprefix tailTrace_7796483
  have hstable : (prefixWord ++ tailWord_7796483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796483).length < 2 ^ (prefixWord ++ tailWord_7796483).sum := by decide
  have hdescent : baseEnd_7796483 < baseStart_7796483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796501 : List Nat := [1, 3, 2, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_7796501 : Nat := 118140960795 + 7796501 * 2 ^ 59
def prefixEnd_7796501 : Nat := 4983230072969 + 3 ^ 40 * 7796501 * 2
def baseEnd_7796501 : Nat := 4003352436259505887682051

theorem tailTrace_7796501 : CollatzResearch.WordTrace tailWord_7796501 prefixEnd_7796501 4003352436259505887682051 := by
  unfold tailWord_7796501
  simp only [CollatzResearch.WordTrace]
  refine ⟨284361752727615888206885357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189574501818410592137923571 284361752727615888206885357)
  ·
    refine ⟨106635657272855958077582009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284361752727615888206885357 106635657272855958077582009)
    ·
      refine ⟨79976742954641968558186507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106635657272855958077582009 79976742954641968558186507)
      ·
        refine ⟨119965114431962952837279761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79976742954641968558186507 119965114431962952837279761)
        ·
          refine ⟨89973835823972214627959821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119965114431962952837279761 89973835823972214627959821)
          ·
            refine ⟨33740188433989580485484933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89973835823972214627959821 33740188433989580485484933)
            ·
              refine ⟨6326285331373046341028425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33740188433989580485484933 6326285331373046341028425)
              ·
                refine ⟨4744713998529784755771319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326285331373046341028425 4744713998529784755771319)
                ·
                  refine ⟨7117070997794677133656979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744713998529784755771319 7117070997794677133656979)
                  ·
                    refine ⟨10675606496692015700485469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7117070997794677133656979 10675606496692015700485469)
                    ·
                      refine ⟨4003352436259505887682051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10675606496692015700485469 4003352436259505887682051)
                      ·
                        rfl

theorem cell23_7796501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_7796501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796501 prefixEnd_7796501 := by exact prefixLift 7796501
  have htrace : WordTrace (prefixWord ++ tailWord_7796501) baseStart_7796501 baseEnd_7796501 := by
    simpa [prefixWord, tailWord_7796501, baseEnd_7796501] using wordTrace_append hprefix tailTrace_7796501
  have hstable : (prefixWord ++ tailWord_7796501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796501).length < 2 ^ (prefixWord ++ tailWord_7796501).sum := by decide
  have hdescent : baseEnd_7796501 < baseStart_7796501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796517 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_7796517 : Nat := 118140960795 + 7796517 * 2 ^ 59
def prefixEnd_7796517 : Nat := 4983230072969 + 3 ^ 40 * 7796517 * 2
def baseEnd_7796517 : Nat := 1334453550649992608360659

theorem tailTrace_7796517 : CollatzResearch.WordTrace tailWord_7796517 prefixEnd_7796517 1334453550649992608360659 := by
  unfold tailWord_7796517
  simp only [CollatzResearch.WordTrace]
  refine ⟨284362336295557922939467805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189574890863705281959645203 284362336295557922939467805)
  ·
    refine ⟨106635876110834221102300427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284362336295557922939467805 106635876110834221102300427)
    ·
      refine ⟨159953814166251331653450641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106635876110834221102300427 159953814166251331653450641)
      ·
        refine ⟨119965360624688498740087981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159953814166251331653450641 119965360624688498740087981)
        ·
          refine ⟨44987010234258187027532993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119965360624688498740087981 44987010234258187027532993)
          ·
            refine ⟨33740257675693640270649745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44987010234258187027532993 33740257675693640270649745)
            ·
              refine ⟨25305193256770230202987309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33740257675693640270649745 25305193256770230202987309)
              ·
                refine ⟨9489447471288836326120241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25305193256770230202987309 9489447471288836326120241)
                ·
                  refine ⟨7117085603466627244590181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9489447471288836326120241 7117085603466627244590181)
                  ·
                    refine ⟨1334453550649992608360659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7117085603466627244590181 1334453550649992608360659)
                    ·
                      rfl

theorem cell23_7796517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_7796517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796517 prefixEnd_7796517 := by exact prefixLift 7796517
  have htrace : WordTrace (prefixWord ++ tailWord_7796517) baseStart_7796517 baseEnd_7796517 := by
    simpa [prefixWord, tailWord_7796517, baseEnd_7796517] using wordTrace_append hprefix tailTrace_7796517
  have hstable : (prefixWord ++ tailWord_7796517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796517).length < 2 ^ (prefixWord ++ tailWord_7796517).sum := by decide
  have hdescent : baseEnd_7796517 < baseStart_7796517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796524 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 3, 2, 2]
def baseStart_7796524 : Nat := 118140960795 + 7796524 * 2 ^ 59
def prefixEnd_7796524 : Nat := 4983230072969 + 3 ^ 40 * 7796524 * 2
def baseEnd_7796524 : Nat := 4003364246314559297694445

theorem tailTrace_7796524 : CollatzResearch.WordTrace tailWord_7796524 prefixEnd_7796524 4003364246314559297694445 := by
  unfold tailWord_7796524
  simp only [CollatzResearch.WordTrace]
  refine ⟨142181295803266281567486313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189575061071021708756648417 142181295803266281567486313)
  ·
    refine ⟨106635971852449711175614735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142181295803266281567486313 106635971852449711175614735)
    ·
      refine ⟨159953957778674566763422103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106635971852449711175614735 159953957778674566763422103)
      ·
        refine ⟨239930936668011850145133155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159953957778674566763422103 239930936668011850145133155)
        ·
          refine ⟨359896405002017775217699733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239930936668011850145133155 359896405002017775217699733)
          ·
            refine ⟨16870143984469583213329675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 359896405002017775217699733 16870143984469583213329675)
            ·
              refine ⟨25305215976704374819994513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16870143984469583213329675 25305215976704374819994513)
              ·
                refine ⟨18978911982528281114995885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25305215976704374819994513 18978911982528281114995885)
                ·
                  refine ⟨7117091993448105418123457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18978911982528281114995885 7117091993448105418123457)
                  ·
                    refine ⟨5337818995086079063592593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7117091993448105418123457 5337818995086079063592593)
                    ·
                      refine ⟨4003364246314559297694445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337818995086079063592593 4003364246314559297694445)
                      ·
                        rfl

theorem cell23_7796524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_7796524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796524 prefixEnd_7796524 := by exact prefixLift 7796524
  have htrace : WordTrace (prefixWord ++ tailWord_7796524) baseStart_7796524 baseEnd_7796524 := by
    simpa [prefixWord, tailWord_7796524, baseEnd_7796524] using wordTrace_append hprefix tailTrace_7796524
  have hstable : (prefixWord ++ tailWord_7796524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796524).length < 2 ^ (prefixWord ++ tailWord_7796524).sum := by decide
  have hdescent : baseEnd_7796524 < baseStart_7796524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796541 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7796541 : Nat := 118140960795 + 7796541 * 2 ^ 59
def prefixEnd_7796541 : Nat := 4983230072969 + 3 ^ 40 * 7796541 * 2
def baseEnd_7796541 : Nat := 4003372975485685731181867

theorem tailTrace_7796541 : CollatzResearch.WordTrace tailWord_7796541 prefixEnd_7796541 4003372975485685731181867 := by
  unfold tailWord_7796541
  simp only [CollatzResearch.WordTrace]
  refine ⟨284363211647470975038341477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189575474431647316692227651 284363211647470975038341477)
  ·
    refine ⟨53318102183900807819689027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284363211647470975038341477 53318102183900807819689027)
    ·
      refine ⟨79977153275851211729533541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53318102183900807819689027 79977153275851211729533541)
      ·
        refine ⟨14995716239222102199287539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79977153275851211729533541 14995716239222102199287539)
        ·
          refine ⟨22493574358833153298931309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14995716239222102199287539 22493574358833153298931309)
          ·
            refine ⟨8435090384562432487099241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22493574358833153298931309 8435090384562432487099241)
            ·
              refine ⟨6326317788421824365324431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435090384562432487099241 6326317788421824365324431)
              ·
                refine ⟨9489476682632736547986647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326317788421824365324431 9489476682632736547986647)
                ·
                  refine ⟨14234215023949104821979971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9489476682632736547986647 14234215023949104821979971)
                  ·
                    refine ⟨21351322535923657232969957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14234215023949104821979971 21351322535923657232969957)
                    ·
                      refine ⟨4003372975485685731181867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21351322535923657232969957 4003372975485685731181867)
                      ·
                        rfl

theorem cell23_7796541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7796541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796541 prefixEnd_7796541 := by exact prefixLift 7796541
  have htrace : WordTrace (prefixWord ++ tailWord_7796541) baseStart_7796541 baseEnd_7796541 := by
    simpa [prefixWord, tailWord_7796541, baseEnd_7796541] using wordTrace_append hprefix tailTrace_7796541
  have hstable : (prefixWord ++ tailWord_7796541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796541).length < 2 ^ (prefixWord ++ tailWord_7796541).sum := by decide
  have hdescent : baseEnd_7796541 < baseStart_7796541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796631 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 2, 2, 2]
def baseStart_7796631 : Nat := 118140960795 + 7796631 * 2 ^ 59
def prefixEnd_7796631 : Nat := 4983230072969 + 3 ^ 40 * 7796631 * 2
def baseEnd_7796631 : Nat := 4003419188744590379056453

theorem tailTrace_7796631 : CollatzResearch.WordTrace tailWord_7796631 prefixEnd_7796631 4003419188744590379056453 := by
  unfold tailWord_7796631
  simp only [CollatzResearch.WordTrace]
  refine ⟨284366494217144920409117747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189577662811429946939411831 284366494217144920409117747)
  ·
    refine ⟨426549741325717380613676621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284366494217144920409117747 426549741325717380613676621)
    ·
      refine ⟨159956152997144017730128733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426549741325717380613676621 159956152997144017730128733)
      ·
        refine ⟨59983557373929006648798275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159956152997144017730128733 59983557373929006648798275)
        ·
          refine ⟨89975336060893509973197413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59983557373929006648798275 89975336060893509973197413)
          ·
            refine ⟨16870375511417533119974515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89975336060893509973197413 16870375511417533119974515)
            ·
              refine ⟨25305563267126299679961773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16870375511417533119974515 25305563267126299679961773)
              ·
                refine ⟨9489586225172362379985665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25305563267126299679961773 9489586225172362379985665)
                ·
                  refine ⟨7117189668879271784989249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9489586225172362379985665 7117189668879271784989249)
                  ·
                    refine ⟨5337892251659453838741937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7117189668879271784989249 5337892251659453838741937)
                    ·
                      refine ⟨4003419188744590379056453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337892251659453838741937 4003419188744590379056453)
                      ·
                        rfl

theorem cell23_7796631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_7796631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796631 prefixEnd_7796631 := by exact prefixLift 7796631
  have htrace : WordTrace (prefixWord ++ tailWord_7796631) baseStart_7796631 baseEnd_7796631 := by
    simpa [prefixWord, tailWord_7796631, baseEnd_7796631] using wordTrace_append hprefix tailTrace_7796631
  have hstable : (prefixWord ++ tailWord_7796631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796631).length < 2 ^ (prefixWord ++ tailWord_7796631).sum := by decide
  have hdescent : baseEnd_7796631 < baseStart_7796631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796648 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7796648 : Nat := 118140960795 + 7796648 * 2 ^ 59
def prefixEnd_7796648 : Nat := 4983230072969 + 3 ^ 40 * 7796648 * 2
def baseEnd_7796648 : Nat := 4003427917915716812543875

theorem tailTrace_7796648 : CollatzResearch.WordTrace tailWord_7796648 prefixEnd_7796648 4003427917915716812543875 := by
  unfold tailWord_7796648
  simp only [CollatzResearch.WordTrace]
  refine ⟨142183557129041666156243299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189578076172055554874991065 142183557129041666156243299)
  ·
    refine ⟨213275335693562499234364949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142183557129041666156243299 213275335693562499234364949)
    ·
      refine ⟨9997281360635742151610857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213275335693562499234364949 9997281360635742151610857)
      ·
        refine ⟨7497961020476806613708143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9997281360635742151610857 7497961020476806613708143)
        ·
          refine ⟨11246941530715209920562215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7497961020476806613708143 11246941530715209920562215)
          ·
            refine ⟨16870412296072814880843323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11246941530715209920562215 16870412296072814880843323)
            ·
              refine ⟨25305618444109222321264985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16870412296072814880843323 25305618444109222321264985)
              ·
                refine ⟨18979213833081916740948739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25305618444109222321264985 18979213833081916740948739)
                ·
                  refine ⟨28468820749622875111423109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18979213833081916740948739 28468820749622875111423109)
                  ·
                    refine ⟨5337903890554289083391833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28468820749622875111423109 5337903890554289083391833)
                    ·
                      refine ⟨4003427917915716812543875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5337903890554289083391833 4003427917915716812543875)
                      ·
                        rfl

theorem cell23_7796648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7796648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796648 prefixEnd_7796648 := by exact prefixLift 7796648
  have htrace : WordTrace (prefixWord ++ tailWord_7796648) baseStart_7796648 baseEnd_7796648 := by
    simpa [prefixWord, tailWord_7796648, baseEnd_7796648] using wordTrace_append hprefix tailTrace_7796648
  have hstable : (prefixWord ++ tailWord_7796648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796648).length < 2 ^ (prefixWord ++ tailWord_7796648).sum := by decide
  have hdescent : baseEnd_7796648 < baseStart_7796648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796701 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7796701 : Nat := 118140960795 + 7796701 * 2 ^ 59
def prefixEnd_7796701 : Nat := 4983230072969 + 3 ^ 40 * 7796701 * 2
def baseEnd_7796701 : Nat := 1334485044130135035060377

theorem tailTrace_7796701 : CollatzResearch.WordTrace tailWord_7796701 prefixEnd_7796701 1334485044130135035060377 := by
  unfold tailWord_7796701
  simp only [CollatzResearch.WordTrace]
  refine ⟨284369047326891322364165957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189579364884594214909443971 284369047326891322364165957)
  ·
    refine ⟨53319196373792122943281117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284369047326891322364165957 53319196373792122943281117)
    ·
      refine ⟨19994698640172046103730419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53319196373792122943281117 19994698640172046103730419)
      ·
        refine ⟨29992047960258069155595629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19994698640172046103730419 29992047960258069155595629)
        ·
          refine ⟨11247017985096775933348361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29992047960258069155595629 11247017985096775933348361)
          ·
            refine ⟨8435263488822581950011271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11247017985096775933348361 8435263488822581950011271)
            ·
              refine ⟨12652895233233872925016907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435263488822581950011271 12652895233233872925016907)
              ·
                refine ⟨18979342849850809387525361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12652895233233872925016907 18979342849850809387525361)
                ·
                  refine ⟨14234507137388107040644021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18979342849850809387525361 14234507137388107040644021)
                  ·
                    refine ⟨1334485044130135035060377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14234507137388107040644021 1334485044130135035060377)
                    ·
                      rfl

theorem cell23_7796701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7796701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796701 prefixEnd_7796701 := by exact prefixLift 7796701
  have htrace : WordTrace (prefixWord ++ tailWord_7796701) baseStart_7796701 baseEnd_7796701 := by
    simpa [prefixWord, tailWord_7796701, baseEnd_7796701] using wordTrace_append hprefix tailTrace_7796701
  have hstable : (prefixWord ++ tailWord_7796701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796701).length < 2 ^ (prefixWord ++ tailWord_7796701).sum := by decide
  have hdescent : baseEnd_7796701 < baseStart_7796701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796744 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 6]
def baseStart_7796744 : Nat := 118140960795 + 7796744 * 2 ^ 59
def prefixEnd_7796744 : Nat := 4983230072969 + 3 ^ 40 * 7796744 * 2
def baseEnd_7796744 : Nat := 444830801339838715215937

theorem tailTrace_7796744 : CollatzResearch.WordTrace tailWord_7796744 prefixEnd_7796744 444830801339838715215937 := by
  unfold tailWord_7796744
  simp only [CollatzResearch.WordTrace]
  refine ⟨142185307832867770353990643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189580410443823693805320857 142185307832867770353990643)
  ·
    refine ⟨213277961749301655530985965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142185307832867770353990643 213277961749301655530985965)
    ·
      refine ⟨79979235655988120824119737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213277961749301655530985965 79979235655988120824119737)
      ·
        refine ⟨59984426741991090618089803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79979235655988120824119737 59984426741991090618089803)
        ·
          refine ⟨89976640112986635927134705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59984426741991090618089803 89976640112986635927134705)
          ·
            refine ⟨67482480084739976945351029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89976640112986635927134705 67482480084739976945351029)
            ·
              refine ⟨6326482507944372838626659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67482480084739976945351029 6326482507944372838626659)
              ·
                refine ⟨9489723761916559257939989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326482507944372838626659 9489723761916559257939989)
                ·
                  refine ⟨444830801339838715215937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9489723761916559257939989 444830801339838715215937)
                  ·
                    rfl

theorem cell23_7796744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 6].length) (baseStart_7796744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796744 prefixEnd_7796744 := by exact prefixLift 7796744
  have htrace : WordTrace (prefixWord ++ tailWord_7796744) baseStart_7796744 baseEnd_7796744 := by
    simpa [prefixWord, tailWord_7796744, baseEnd_7796744] using wordTrace_append hprefix tailTrace_7796744
  have hstable : (prefixWord ++ tailWord_7796744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796744).length < 2 ^ (prefixWord ++ tailWord_7796744).sum := by decide
  have hdescent : baseEnd_7796744 < baseStart_7796744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796807 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_7796807 : Nat := 118140960795 + 7796807 * 2 ^ 59
def prefixEnd_7796807 : Nat := 4983230072969 + 3 ^ 40 * 7796807 * 2
def baseEnd_7796807 : Nat := 4003509561339781690455643

theorem tailTrace_7796807 : CollatzResearch.WordTrace tailWord_7796807 prefixEnd_7796807 4003509561339781690455643 := by
  unfold tailWord_7796807
  simp only [CollatzResearch.WordTrace]
  refine ⟨284372913464507302467524675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189581942309671534978349783 284372913464507302467524675)
  ·
    refine ⟨426559370196760953701287013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284372913464507302467524675 426559370196760953701287013)
    ·
      refine ⟨79979881911892678818991315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426559370196760953701287013 79979881911892678818991315)
      ·
        refine ⟨119969822867839018228486973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79979881911892678818991315 119969822867839018228486973)
        ·
          refine ⟨44988683575439631835682615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119969822867839018228486973 44988683575439631835682615)
          ·
            refine ⟨67483025363159447753523923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44988683575439631835682615 67483025363159447753523923)
            ·
              refine ⟨101224538044739171630285885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67483025363159447753523923 101224538044739171630285885)
              ·
                refine ⟨37959201766777189361357207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101224538044739171630285885 37959201766777189361357207)
                ·
                  refine ⟨56938802650165784042035811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37959201766777189361357207 56938802650165784042035811)
                  ·
                    refine ⟨85408203975248676063053717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56938802650165784042035811 85408203975248676063053717)
                    ·
                      refine ⟨4003509561339781690455643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85408203975248676063053717 4003509561339781690455643)
                      ·
                        rfl

theorem cell23_7796807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_7796807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796807 prefixEnd_7796807 := by exact prefixLift 7796807
  have htrace : WordTrace (prefixWord ++ tailWord_7796807) baseStart_7796807 baseEnd_7796807 := by
    simpa [prefixWord, tailWord_7796807, baseEnd_7796807] using wordTrace_append hprefix tailTrace_7796807
  have hstable : (prefixWord ++ tailWord_7796807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796807).length < 2 ^ (prefixWord ++ tailWord_7796807).sum := by decide
  have hdescent : baseEnd_7796807 < baseStart_7796807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796824 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_7796824 : Nat := 118140960795 + 7796824 * 2 ^ 59
def prefixEnd_7796824 : Nat := 4983230072969 + 3 ^ 40 * 7796824 * 2
def baseEnd_7796824 : Nat := 4003518290510908123943065

theorem tailTrace_7796824 : CollatzResearch.WordTrace tailWord_7796824 prefixEnd_7796824 4003518290510908123943065 := by
  unfold tailWord_7796824
  simp only [CollatzResearch.WordTrace]
  refine ⟨142186766752722857185446763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189582355670297142913929017 142186766752722857185446763)
  ·
    refine ⟨213280150129084285778170145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142186766752722857185446763 213280150129084285778170145)
    ·
      refine ⟨159960112596813214333627609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213280150129084285778170145 159960112596813214333627609)
      ·
        refine ⟨119970084447609910750220707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159960112596813214333627609 119970084447609910750220707)
        ·
          refine ⟨179955126671414866125331061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119970084447609910750220707 179955126671414866125331061)
          ·
            refine ⟨16870793125445143699249787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179955126671414866125331061 16870793125445143699249787)
            ·
              refine ⟨25306189688167715548874681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16870793125445143699249787 25306189688167715548874681)
              ·
                refine ⟨18979642266125786661656011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25306189688167715548874681 18979642266125786661656011)
                ·
                  refine ⟨28469463399188679992484017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18979642266125786661656011 28469463399188679992484017)
                  ·
                    refine ⟨21352097549391509994363013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28469463399188679992484017 21352097549391509994363013)
                    ·
                      refine ⟨4003518290510908123943065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21352097549391509994363013 4003518290510908123943065)
                      ·
                        rfl

theorem cell23_7796824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_7796824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796824 prefixEnd_7796824 := by exact prefixLift 7796824
  have htrace : WordTrace (prefixWord ++ tailWord_7796824) baseStart_7796824 baseEnd_7796824 := by
    simpa [prefixWord, tailWord_7796824, baseEnd_7796824] using wordTrace_append hprefix tailTrace_7796824
  have hstable : (prefixWord ++ tailWord_7796824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796824).length < 2 ^ (prefixWord ++ tailWord_7796824).sum := by decide
  have hdescent : baseEnd_7796824 < baseStart_7796824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796828 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_7796828 : Nat := 118140960795 + 7796828 * 2 ^ 59
def prefixEnd_7796828 : Nat := 4983230072969 + 3 ^ 40 * 7796828 * 2
def baseEnd_7796828 : Nat := 4003520344433526108293047

theorem tailTrace_7796828 : CollatzResearch.WordTrace tailWord_7796828 prefixEnd_7796828 4003520344433526108293047 := by
  unfold tailWord_7796828
  simp only [CollatzResearch.WordTrace]
  refine ⟨142186839698715611527019569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189582452931620815369359425 142186839698715611527019569)
  ·
    refine ⟨106640129774036708645264677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142186839698715611527019569 106640129774036708645264677)
    ·
      refine ⟨19995024332631882870987127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106640129774036708645264677 19995024332631882870987127)
      ·
        refine ⟨29992536498947824306480691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19995024332631882870987127 29992536498947824306480691)
        ·
          refine ⟨44988804748421736459721037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29992536498947824306480691 44988804748421736459721037)
          ·
            refine ⟨16870801780658151172395389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44988804748421736459721037 16870801780658151172395389)
            ·
              refine ⟨6326550667746806689648271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16870801780658151172395389 6326550667746806689648271)
              ·
                refine ⟨9489826001620210034472407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326550667746806689648271 9489826001620210034472407)
                ·
                  refine ⟨14234739002430315051708611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9489826001620210034472407 14234739002430315051708611)
                  ·
                    refine ⟨21352108503645472577562917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14234739002430315051708611 21352108503645472577562917)
                    ·
                      refine ⟨4003520344433526108293047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21352108503645472577562917 4003520344433526108293047)
                      ·
                        rfl

theorem cell23_7796828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_7796828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796828 prefixEnd_7796828 := by exact prefixLift 7796828
  have htrace : WordTrace (prefixWord ++ tailWord_7796828) baseStart_7796828 baseEnd_7796828 := by
    simpa [prefixWord, tailWord_7796828, baseEnd_7796828] using wordTrace_append hprefix tailTrace_7796828
  have hstable : (prefixWord ++ tailWord_7796828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796828).length < 2 ^ (prefixWord ++ tailWord_7796828).sum := by decide
  have hdescent : baseEnd_7796828 < baseStart_7796828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796834 : List Nat := [3, 3, 2, 2, 2, 11]
def baseStart_7796834 : Nat := 118140960795 + 7796834 * 2 ^ 59
def prefixEnd_7796834 : Nat := 4983230072969 + 3 ^ 40 * 7796834 * 2
def baseEnd_7796834 : Nat := 16475405042458654670033

theorem tailTrace_7796834 : CollatzResearch.WordTrace tailWord_7796834 prefixEnd_7796834 16475405042458654670033 := by
  unfold tailWord_7796834
  simp only [CollatzResearch.WordTrace]
  refine ⟨71093474558852371519689389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189582598823606324052505037 71093474558852371519689389)
  ·
    refine ⟨26660052959569639319883521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71093474558852371519689389 26660052959569639319883521)
    ·
      refine ⟨19995039719677229489912641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26660052959569639319883521 19995039719677229489912641)
      ·
        refine ⟨14996279789757922117434481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19995039719677229489912641 14996279789757922117434481)
        ·
          refine ⟨11247209842318441588075861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14996279789757922117434481 11247209842318441588075861)
          ·
            refine ⟨16475405042458654670033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11247209842318441588075861 16475405042458654670033)
            ·
              rfl

theorem cell23_7796834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 11].length) (baseStart_7796834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796834 prefixEnd_7796834 := by exact prefixLift 7796834
  have htrace : WordTrace (prefixWord ++ tailWord_7796834) baseStart_7796834 baseEnd_7796834 := by
    simpa [prefixWord, tailWord_7796834, baseEnd_7796834] using wordTrace_append hprefix tailTrace_7796834
  have hstable : (prefixWord ++ tailWord_7796834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796834).length < 2 ^ (prefixWord ++ tailWord_7796834).sum := by decide
  have hdescent : baseEnd_7796834 < baseStart_7796834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796845 : List Nat := [1, 5, 1, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_7796845 : Nat := 118140960795 + 7796845 * 2 ^ 59
def prefixEnd_7796845 : Nat := 4983230072969 + 3 ^ 40 * 7796845 * 2
def baseEnd_7796845 : Nat := 4003529073604652541780469

theorem tailTrace_7796845 : CollatzResearch.WordTrace tailWord_7796845 prefixEnd_7796845 4003529073604652541780469 := by
  unfold tailWord_7796845
  simp only [CollatzResearch.WordTrace]
  refine ⟨284374299438369634957407989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189582866292246423304938659 284374299438369634957407989)
  ·
    refine ⟨26660090572347153277256999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284374299438369634957407989 26660090572347153277256999)
    ·
      refine ⟨39990135858520729915885499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26660090572347153277256999 39990135858520729915885499)
      ·
        refine ⟨59985203787781094873828249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39990135858520729915885499 59985203787781094873828249)
        ·
          refine ⟨44988902840835821155371187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59985203787781094873828249 44988902840835821155371187)
          ·
            refine ⟨67483354261253731733056781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44988902840835821155371187 67483354261253731733056781)
            ·
              refine ⟨25306257847970149399896293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67483354261253731733056781 25306257847970149399896293)
              ·
                refine ⟨4744923346494403012480555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25306257847970149399896293 4744923346494403012480555)
                ·
                  refine ⟨7117385019741604518720833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744923346494403012480555 7117385019741604518720833)
                  ·
                    refine ⟨5338038764806203389040625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7117385019741604518720833 5338038764806203389040625)
                    ·
                      refine ⟨4003529073604652541780469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338038764806203389040625 4003529073604652541780469)
                      ·
                        rfl

theorem cell23_7796845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_7796845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796845 prefixEnd_7796845 := by exact prefixLift 7796845
  have htrace : WordTrace (prefixWord ++ tailWord_7796845) baseStart_7796845 baseEnd_7796845 := by
    simpa [prefixWord, tailWord_7796845, baseEnd_7796845] using wordTrace_append hprefix tailTrace_7796845
  have hstable : (prefixWord ++ tailWord_7796845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796845).length < 2 ^ (prefixWord ++ tailWord_7796845).sum := by decide
  have hdescent : baseEnd_7796845 < baseStart_7796845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796847 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 2, 7]
def baseStart_7796847 : Nat := 118140960795 + 7796847 * 2 ^ 59
def prefixEnd_7796847 : Nat := 4983230072969 + 3 ^ 40 * 7796847 * 2
def baseEnd_7796847 : Nat := 1334510033521987177985153

theorem tailTrace_7796847 : CollatzResearch.WordTrace tailWord_7796847 prefixEnd_7796847 1334510033521987177985153 := by
  unfold tailWord_7796847
  simp only [CollatzResearch.WordTrace]
  refine ⟨284374372384362389298980795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189582914922908259532653863 284374372384362389298980795)
  ·
    refine ⟨426561558576543583948471193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284374372384362389298980795 426561558576543583948471193)
    ·
      refine ⟨319921168932407687961353395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426561558576543583948471193 319921168932407687961353395)
      ·
        refine ⟨479881753398611531942030093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319921168932407687961353395 479881753398611531942030093)
        ·
          refine ⟨179955657524479324478261285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479881753398611531942030093 179955657524479324478261285)
          ·
            refine ⟨33741685785839873339673991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179955657524479324478261285 33741685785839873339673991)
            ·
              refine ⟨50612528678759810009510987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33741685785839873339673991 50612528678759810009510987)
              ·
                refine ⟨75918793018139715014266481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50612528678759810009510987 75918793018139715014266481)
                ·
                  refine ⟨56939094763604786260699861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75918793018139715014266481 56939094763604786260699861)
                  ·
                    refine ⟨1334510033521987177985153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56939094763604786260699861 1334510033521987177985153)
                    ·
                      rfl

theorem cell23_7796847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_7796847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796847 prefixEnd_7796847 := by exact prefixLift 7796847
  have htrace : WordTrace (prefixWord ++ tailWord_7796847) baseStart_7796847 baseEnd_7796847 := by
    simpa [prefixWord, tailWord_7796847, baseEnd_7796847] using wordTrace_append hprefix tailTrace_7796847
  have hstable : (prefixWord ++ tailWord_7796847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796847).length < 2 ^ (prefixWord ++ tailWord_7796847).sum := by decide
  have hdescent : baseEnd_7796847 < baseStart_7796847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796861 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_7796861 : Nat := 118140960795 + 7796861 * 2 ^ 59
def prefixEnd_7796861 : Nat := 4983230072969 + 3 ^ 40 * 7796861 * 2
def baseEnd_7796861 : Nat := 4003537289295124479180395

theorem tailTrace_7796861 : CollatzResearch.WordTrace tailWord_7796861 prefixEnd_7796861 4003537289295124479180395 := by
  unfold tailWord_7796861
  simp only [CollatzResearch.WordTrace]
  refine ⟨284374883006311669689990437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189583255337541113126660291 284374883006311669689990437)
  ·
    refine ⟨53320290563683438066873207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284374883006311669689990437 53320290563683438066873207)
    ·
      refine ⟨79980435845525157100309811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53320290563683438066873207 79980435845525157100309811)
      ·
        refine ⟨119970653768287735650464717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79980435845525157100309811 119970653768287735650464717)
        ·
          refine ⟨44988995163107900868924269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119970653768287735650464717 44988995163107900868924269)
          ·
            refine ⟨16870873186165462825846601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44988995163107900868924269 16870873186165462825846601)
            ·
              refine ⟨12653154889624097119384951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16870873186165462825846601 12653154889624097119384951)
              ·
                refine ⟨18979732334436145679077427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12653154889624097119384951 18979732334436145679077427)
                ·
                  refine ⟨28469598501654218518616141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18979732334436145679077427 28469598501654218518616141)
                  ·
                    refine ⟨10676099438120331944481053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28469598501654218518616141 10676099438120331944481053)
                    ·
                      refine ⟨4003537289295124479180395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10676099438120331944481053 4003537289295124479180395)
                      ·
                        rfl

theorem cell23_7796861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_7796861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796861 prefixEnd_7796861 := by exact prefixLift 7796861
  have htrace : WordTrace (prefixWord ++ tailWord_7796861) baseStart_7796861 baseEnd_7796861 := by
    simpa [prefixWord, tailWord_7796861, baseEnd_7796861] using wordTrace_append hprefix tailTrace_7796861
  have hstable : (prefixWord ++ tailWord_7796861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796861).length < 2 ^ (prefixWord ++ tailWord_7796861).sum := by decide
  have hdescent : baseEnd_7796861 < baseStart_7796861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796871 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_7796871 : Nat := 118140960795 + 7796871 * 2 ^ 59
def prefixEnd_7796871 : Nat := 4983230072969 + 3 ^ 40 * 7796871 * 2
def baseEnd_7796871 : Nat := 4003542424101669440055349

theorem tailTrace_7796871 : CollatzResearch.WordTrace tailWord_7796871 prefixEnd_7796871 4003542424101669440055349 := by
  unfold tailWord_7796871
  simp only [CollatzResearch.WordTrace]
  refine ⟨284375247736275441397854467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189583498490850294265236311 284375247736275441397854467)
  ·
    refine ⟨426562871604413162096781701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284375247736275441397854467 426562871604413162096781701)
    ·
      refine ⟨79980538425827467893146569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426562871604413162096781701 79980538425827467893146569)
      ·
        refine ⟨59985403819370600919859927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79980538425827467893146569 59985403819370600919859927)
        ·
          refine ⟨89978105729055901379789891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59985403819370600919859927 89978105729055901379789891)
          ·
            refine ⟨134967158593583852069684837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89978105729055901379789891 134967158593583852069684837)
            ·
              refine ⟨25306342236296972263065907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134967158593583852069684837 25306342236296972263065907)
              ·
                refine ⟨37959513354445458394598861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25306342236296972263065907 37959513354445458394598861)
                ·
                  refine ⟨14234817507917046897974573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37959513354445458394598861 14234817507917046897974573)
                  ·
                    refine ⟨5338056565468892586740465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14234817507917046897974573 5338056565468892586740465)
                    ·
                      refine ⟨4003542424101669440055349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338056565468892586740465 4003542424101669440055349)
                      ·
                        rfl

theorem cell23_7796871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_7796871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796871 prefixEnd_7796871 := by exact prefixLift 7796871
  have htrace : WordTrace (prefixWord ++ tailWord_7796871) baseStart_7796871 baseEnd_7796871 := by
    simpa [prefixWord, tailWord_7796871, baseEnd_7796871] using wordTrace_append hprefix tailTrace_7796871
  have hstable : (prefixWord ++ tailWord_7796871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796871).length < 2 ^ (prefixWord ++ tailWord_7796871).sum := by decide
  have hdescent : baseEnd_7796871 < baseStart_7796871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796895 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7796895 : Nat := 118140960795 + 7796895 * 2 ^ 59
def prefixEnd_7796895 : Nat := 4983230072969 + 3 ^ 40 * 7796895 * 2
def baseEnd_7796895 : Nat := 4003554747637377346155239

theorem tailTrace_7796895 : CollatzResearch.WordTrace tailWord_7796895 prefixEnd_7796895 4003554747637377346155239 := by
  unfold tailWord_7796895
  simp only [CollatzResearch.WordTrace]
  refine ⟨284376123088188493496728139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189584082058792328997818759 284376123088188493496728139)
  ·
    refine ⟨426564184632282740245092209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284376123088188493496728139 426564184632282740245092209)
    ·
      refine ⟨319923138474212055183819157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426564184632282740245092209 319923138474212055183819157)
      ·
        refine ⟨14996397115978690086741523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 319923138474212055183819157 14996397115978690086741523)
        ·
          refine ⟨22494595673968035130112285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14996397115978690086741523 22494595673968035130112285)
          ·
            refine ⟨8435473377738013173792107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22494595673968035130112285 8435473377738013173792107)
            ·
              refine ⟨12653210066607019760688161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435473377738013173792107 12653210066607019760688161)
              ·
                refine ⟨9489907549955264820516121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12653210066607019760688161 9489907549955264820516121)
                ·
                  refine ⟨7117430662466448615387091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9489907549955264820516121 7117430662466448615387091)
                  ·
                    refine ⟨10676145993699672923080637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7117430662466448615387091 10676145993699672923080637)
                    ·
                      refine ⟨4003554747637377346155239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10676145993699672923080637 4003554747637377346155239)
                      ·
                        rfl

theorem cell23_7796895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7796895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796895 prefixEnd_7796895 := by exact prefixLift 7796895
  have htrace : WordTrace (prefixWord ++ tailWord_7796895) baseStart_7796895 baseEnd_7796895 := by
    simpa [prefixWord, tailWord_7796895, baseEnd_7796895] using wordTrace_append hprefix tailTrace_7796895
  have hstable : (prefixWord ++ tailWord_7796895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796895).length < 2 ^ (prefixWord ++ tailWord_7796895).sum := by decide
  have hdescent : baseEnd_7796895 < baseStart_7796895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796914 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_7796914 : Nat := 118140960795 + 7796914 * 2 ^ 59
def prefixEnd_7796914 : Nat := 4983230072969 + 3 ^ 40 * 7796914 * 2
def baseEnd_7796914 : Nat := 4003564503769812771817651

theorem tailTrace_7796914 : CollatzResearch.WordTrace tailWord_7796914 prefixEnd_7796914 4003564503769812771817651 := by
  unfold tailWord_7796914
  simp only [CollatzResearch.WordTrace]
  refine ⟨71094204018779914935417449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189584544050079773161113197 71094204018779914935417449)
  ·
    refine ⟨53320653014084936201563087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71094204018779914935417449 53320653014084936201563087)
    ·
      refine ⟨79980979521127404302344631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53320653014084936201563087 79980979521127404302344631)
      ·
        refine ⟨119971469281691106453516947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79980979521127404302344631 119971469281691106453516947)
        ·
          refine ⟨179957203922536659680275421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119971469281691106453516947 179957203922536659680275421)
          ·
            refine ⟨67483951470951247380103283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179957203922536659680275421 67483951470951247380103283)
            ·
              refine ⟨101225927206426871070154925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67483951470951247380103283 101225927206426871070154925)
              ·
                refine ⟨37959722702410076651308097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101225927206426871070154925 37959722702410076651308097)
                ·
                  refine ⟨28469792026807557488481073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37959722702410076651308097 28469792026807557488481073)
                  ·
                    refine ⟨21352344020105668116360805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28469792026807557488481073 21352344020105668116360805)
                    ·
                      refine ⟨4003564503769812771817651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21352344020105668116360805 4003564503769812771817651)
                      ·
                        rfl

theorem cell23_7796914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_7796914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796914 prefixEnd_7796914 := by exact prefixLift 7796914
  have htrace : WordTrace (prefixWord ++ tailWord_7796914) baseStart_7796914 baseEnd_7796914 := by
    simpa [prefixWord, tailWord_7796914, baseEnd_7796914] using wordTrace_append hprefix tailTrace_7796914
  have hstable : (prefixWord ++ tailWord_7796914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796914).length < 2 ^ (prefixWord ++ tailWord_7796914).sum := by decide
  have hdescent : baseEnd_7796914 < baseStart_7796914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796954 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_7796954 : Nat := 118140960795 + 7796954 * 2 ^ 59
def prefixEnd_7796954 : Nat := 4983230072969 + 3 ^ 40 * 7796954 * 2
def baseEnd_7796954 : Nat := 1334528347665330871772489

theorem tailTrace_7796954 : CollatzResearch.WordTrace tailWord_7796954 prefixEnd_7796954 1334528347665330871772489 := by
  unfold tailWord_7796954
  simp only [CollatzResearch.WordTrace]
  refine ⟨71094568748743686643281479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189585516663316497715417277 71094568748743686643281479)
  ·
    refine ⟨106641853123115529964922219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71094568748743686643281479 106641853123115529964922219)
    ·
      refine ⟨159962779684673294947383329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106641853123115529964922219 159962779684673294947383329)
      ·
        refine ⟨119972084763504971210537497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159962779684673294947383329 119972084763504971210537497)
        ·
          refine ⟨89979063572628728407903123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119972084763504971210537497 89979063572628728407903123)
          ·
            refine ⟨134968595358943092611854685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89979063572628728407903123 134968595358943092611854685)
            ·
              refine ⟨50613223259603659729445507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134968595358943092611854685 50613223259603659729445507)
              ·
                refine ⟨75919834889405489594168261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50613223259603659729445507 75919834889405489594168261)
                ·
                  refine ⟨14234969041763529298906549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75919834889405489594168261 14234969041763529298906549)
                  ·
                    refine ⟨1334528347665330871772489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14234969041763529298906549 1334528347665330871772489)
                    ·
                      rfl

theorem cell23_7796954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_7796954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796954 prefixEnd_7796954 := by exact prefixLift 7796954
  have htrace : WordTrace (prefixWord ++ tailWord_7796954) baseStart_7796954 baseEnd_7796954 := by
    simpa [prefixWord, tailWord_7796954, baseEnd_7796954] using wordTrace_append hprefix tailTrace_7796954
  have hstable : (prefixWord ++ tailWord_7796954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796954).length < 2 ^ (prefixWord ++ tailWord_7796954).sum := by decide
  have hdescent : baseEnd_7796954 < baseStart_7796954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796961 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_7796961 : Nat := 118140960795 + 7796961 * 2 ^ 59
def prefixEnd_7796961 : Nat := 4983230072969 + 3 ^ 40 * 7796961 * 2
def baseEnd_7796961 : Nat := 4003588637360574087929935

theorem tailTrace_7796961 : CollatzResearch.WordTrace tailWord_7796961 prefixEnd_7796961 4003588637360574087929935 := by
  unfold tailWord_7796961
  simp only [CollatzResearch.WordTrace]
  refine ⟨284378530305949386768630737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189585686870632924512420491 284378530305949386768630737)
  ·
    refine ⟨213283897729462040076473053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284378530305949386768630737 213283897729462040076473053)
    ·
      refine ⟨79981461648548265028677395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213283897729462040076473053 79981461648548265028677395)
      ·
        refine ⟨119972192472822397543016093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79981461648548265028677395 119972192472822397543016093)
        ·
          refine ⟨44989572177308399078631035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119972192472822397543016093 44989572177308399078631035)
          ·
            refine ⟨67484358265962598617946553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44989572177308399078631035 67484358265962598617946553)
            ·
              refine ⟨50613268699471948963459915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67484358265962598617946553 50613268699471948963459915)
              ·
                refine ⟨75919903049207923445189873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50613268699471948963459915 75919903049207923445189873)
                ·
                  refine ⟨56939927286905942583892405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75919903049207923445189873 56939927286905942583892405)
                  ·
                    refine ⟨5338118183147432117239913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56939927286905942583892405 5338118183147432117239913)
                    ·
                      refine ⟨4003588637360574087929935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338118183147432117239913 4003588637360574087929935)
                      ·
                        rfl

theorem cell23_7796961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_7796961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796961 prefixEnd_7796961 := by exact prefixLift 7796961
  have htrace : WordTrace (prefixWord ++ tailWord_7796961) baseStart_7796961 baseEnd_7796961 := by
    simpa [prefixWord, tailWord_7796961, baseEnd_7796961] using wordTrace_append hprefix tailTrace_7796961
  have hstable : (prefixWord ++ tailWord_7796961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796961).length < 2 ^ (prefixWord ++ tailWord_7796961).sum := by decide
  have hdescent : baseEnd_7796961 < baseStart_7796961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7796991 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 4]
def baseStart_7796991 : Nat := 118140960795 + 7796991 * 2 ^ 59
def prefixEnd_7796991 : Nat := 4983230072969 + 3 ^ 40 * 7796991 * 2
def baseEnd_7796991 : Nat := 4003604041780208970554797

theorem tailTrace_7796991 : CollatzResearch.WordTrace tailWord_7796991 prefixEnd_7796991 4003604041780208970554797 := by
  unfold tailWord_7796991
  simp only [CollatzResearch.WordTrace]
  refine ⟨284379624495840701892222827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189586416330560467928148551 284379624495840701892222827)
  ·
    refine ⟨426569436743761052838334241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284379624495840701892222827 426569436743761052838334241)
    ·
      refine ⟨319927077557820789628750681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426569436743761052838334241 319927077557820789628750681)
      ·
        refine ⟨239945308168365592221563011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319927077557820789628750681 239945308168365592221563011)
        ·
          refine ⟨359917962252548388332344517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239945308168365592221563011 359917962252548388332344517)
          ·
            refine ⟨67484617922352822812314597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359917962252548388332344517 67484617922352822812314597)
            ·
              refine ⟨12653365860441154277308987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67484617922352822812314597 12653365860441154277308987)
              ·
                refine ⟨18980048790661731415963481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12653365860441154277308987 18980048790661731415963481)
                ·
                  refine ⟨14235036592996298561972611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18980048790661731415963481 14235036592996298561972611)
                  ·
                    refine ⟨21352554889494447842958917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14235036592996298561972611 21352554889494447842958917)
                    ·
                      refine ⟨4003604041780208970554797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21352554889494447842958917 4003604041780208970554797)
                      ·
                        rfl

theorem cell23_7796991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_7796991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7796991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7796991 prefixEnd_7796991 := by exact prefixLift 7796991
  have htrace : WordTrace (prefixWord ++ tailWord_7796991) baseStart_7796991 baseEnd_7796991 := by
    simpa [prefixWord, tailWord_7796991, baseEnd_7796991] using wordTrace_append hprefix tailTrace_7796991
  have hstable : (prefixWord ++ tailWord_7796991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7796991).length < 2 ^ (prefixWord ++ tailWord_7796991).sum := by decide
  have hdescent : baseEnd_7796991 < baseStart_7796991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7796991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797004 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_7797004 : Nat := 118140960795 + 7797004 * 2 ^ 59
def prefixEnd_7797004 : Nat := 4983230072969 + 3 ^ 40 * 7797004 * 2
def baseEnd_7797004 : Nat := 4003610717028717419692237

theorem tailTrace_7797004 : CollatzResearch.WordTrace tailWord_7797004 prefixEnd_7797004 4003610717028717419692237 := by
  unfold tailWord_7797004
  simp only [CollatzResearch.WordTrace]
  refine ⟨142190049322396802556223033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189586732429862403408297377 142190049322396802556223033)
  ·
    refine ⟨106642536991797601917167275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142190049322396802556223033 106642536991797601917167275)
    ·
      refine ⟨159963805487696402875750913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106642536991797601917167275 159963805487696402875750913)
      ·
        refine ⟨119972854115772302156813185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159963805487696402875750913 119972854115772302156813185)
        ·
          refine ⟨89979640586829226617609889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119972854115772302156813185 89979640586829226617609889)
          ·
            refine ⟨67484730440121919963207417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89979640586829226617609889 67484730440121919963207417)
            ·
              refine ⟨50613547830091439972405563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67484730440121919963207417 50613547830091439972405563)
              ·
                refine ⟨75920321745137159958608345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50613547830091439972405563 75920321745137159958608345)
                ·
                  refine ⟨56940241308852869968956259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75920321745137159958608345 56940241308852869968956259)
                  ·
                    refine ⟨85410361963279304953434389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56940241308852869968956259 85410361963279304953434389)
                    ·
                      refine ⟨4003610717028717419692237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85410361963279304953434389 4003610717028717419692237)
                      ·
                        rfl

theorem cell23_7797004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_7797004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797004 prefixEnd_7797004 := by exact prefixLift 7797004
  have htrace : WordTrace (prefixWord ++ tailWord_7797004) baseStart_7797004 baseEnd_7797004 := by
    simpa [prefixWord, tailWord_7797004, baseEnd_7797004] using wordTrace_append hprefix tailTrace_7797004
  have hstable : (prefixWord ++ tailWord_7797004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797004).length < 2 ^ (prefixWord ++ tailWord_7797004).sum := by decide
  have hdescent : baseEnd_7797004 < baseStart_7797004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797068 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 4, 3, 2]
def baseStart_7797068 : Nat := 118140960795 + 7797068 * 2 ^ 59
def prefixEnd_7797068 : Nat := 4983230072969 + 3 ^ 40 * 7797068 * 2
def baseEnd_7797068 : Nat := 4003643579790605169291943

theorem tailTrace_7797068 : CollatzResearch.WordTrace tailWord_7797068 prefixEnd_7797068 4003643579790605169291943 := by
  unfold tailWord_7797068
  simp only [CollatzResearch.WordTrace]
  refine ⟨142191216458280872021387929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189588288611041162695183905 142191216458280872021387929)
  ·
    refine ⟨106643412343710654016040947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142191216458280872021387929 106643412343710654016040947)
    ·
      refine ⟨159965118515565981024061421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106643412343710654016040947 159965118515565981024061421)
      ·
        refine ⟨59986919443337242884023033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159965118515565981024061421 59986919443337242884023033)
        ·
          refine ⟨44990189582502932163017275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59986919443337242884023033 44990189582502932163017275)
          ·
            refine ⟨67485284373754398244525913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44990189582502932163017275 67485284373754398244525913)
            ·
              refine ⟨50613963280315798683394435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67485284373754398244525913 50613963280315798683394435)
              ·
                refine ⟨75920944920473698025091653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50613963280315798683394435 75920944920473698025091653)
                ·
                  refine ⟨14235177172588818379704685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75920944920473698025091653 14235177172588818379704685)
                  ·
                    refine ⟨5338191439720806892389257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14235177172588818379704685 5338191439720806892389257)
                    ·
                      refine ⟨4003643579790605169291943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338191439720806892389257 4003643579790605169291943)
                      ·
                        rfl

theorem cell23_7797068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_7797068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797068 prefixEnd_7797068 := by exact prefixLift 7797068
  have htrace : WordTrace (prefixWord ++ tailWord_7797068) baseStart_7797068 baseEnd_7797068 := by
    simpa [prefixWord, tailWord_7797068, baseEnd_7797068] using wordTrace_append hprefix tailTrace_7797068
  have hstable : (prefixWord ++ tailWord_7797068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797068).length < 2 ^ (prefixWord ++ tailWord_7797068).sum := by decide
  have hdescent : baseEnd_7797068 < baseStart_7797068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797101 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_7797101 : Nat := 118140960795 + 7797101 * 2 ^ 59
def prefixEnd_7797101 : Nat := 4983230072969 + 3 ^ 40 * 7797101 * 2
def baseEnd_7797101 : Nat := 4003660524652203540179291

theorem tailTrace_7797101 : CollatzResearch.WordTrace tailWord_7797101 prefixEnd_7797101 4003660524652203540179291 := by
  unfold tailWord_7797101
  simp only [CollatzResearch.WordTrace]
  refine ⟨284383636525442190678727157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189589091016961460452484771 284383636525442190678727157)
  ·
    refine ⟨26660965924260205376130671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284383636525442190678727157 26660965924260205376130671)
    ·
      refine ⟨39991448886390308064196007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26660965924260205376130671 39991448886390308064196007)
      ·
        refine ⟨59987173329585462096294011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39991448886390308064196007 59987173329585462096294011)
        ·
          refine ⟨89980759994378193144441017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59987173329585462096294011 89980759994378193144441017)
          ·
            refine ⟨67485569995783644858330763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89980759994378193144441017 67485569995783644858330763)
            ·
              refine ⟨101228354993675467287496145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67485569995783644858330763 101228354993675467287496145)
              ·
                refine ⟨75921266245256600465622109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101228354993675467287496145 75921266245256600465622109)
                ·
                  refine ⟨28470474841971225174608291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75921266245256600465622109 28470474841971225174608291)
                  ·
                    refine ⟨42705712262956837761912437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28470474841971225174608291 42705712262956837761912437)
                    ·
                      refine ⟨4003660524652203540179291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42705712262956837761912437 4003660524652203540179291)
                      ·
                        rfl

theorem cell23_7797101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_7797101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797101 prefixEnd_7797101 := by exact prefixLift 7797101
  have htrace : WordTrace (prefixWord ++ tailWord_7797101) baseStart_7797101 baseEnd_7797101 := by
    simpa [prefixWord, tailWord_7797101, baseEnd_7797101] using wordTrace_append hprefix tailTrace_7797101
  have hstable : (prefixWord ++ tailWord_7797101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797101).length < 2 ^ (prefixWord ++ tailWord_7797101).sum := by decide
  have hdescent : baseEnd_7797101 < baseStart_7797101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797109 : List Nat := [1, 3, 4, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_7797109 : Nat := 118140960795 + 7797109 * 2 ^ 59
def prefixEnd_7797109 : Nat := 4983230072969 + 3 ^ 40 * 7797109 * 2
def baseEnd_7797109 : Nat := 4003664632497439508879255

theorem tailTrace_7797109 : CollatzResearch.WordTrace tailWord_7797109 prefixEnd_7797109 4003664632497439508879255 := by
  unfold tailWord_7797109
  simp only [CollatzResearch.WordTrace]
  refine ⟨284383928309413208045018381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189589285539608805363345587 284383928309413208045018381)
  ·
    refine ⟨106643973116029953016881893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284383928309413208045018381 106643973116029953016881893)
    ·
      refine ⟨19995744959255616190665355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106643973116029953016881893 19995744959255616190665355)
      ·
        refine ⟨29993617438883424285998033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19995744959255616190665355 29993617438883424285998033)
        ·
          refine ⟨22495213079162568214498525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29993617438883424285998033 22495213079162568214498525)
          ·
            refine ⟨8435704904685963080436947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22495213079162568214498525 8435704904685963080436947)
            ·
              refine ⟨12653557357028944620655421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435704904685963080436947 12653557357028944620655421)
              ·
                refine ⟨4745084008885854232745783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12653557357028944620655421 4745084008885854232745783)
                ·
                  refine ⟨7117626013328781349118675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745084008885854232745783 7117626013328781349118675)
                  ·
                    refine ⟨10676439019993172023678013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7117626013328781349118675 10676439019993172023678013)
                    ·
                      refine ⟨4003664632497439508879255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10676439019993172023678013 4003664632497439508879255)
                      ·
                        rfl

theorem cell23_7797109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_7797109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797109 prefixEnd_7797109 := by exact prefixLift 7797109
  have htrace : WordTrace (prefixWord ++ tailWord_7797109) baseStart_7797109 baseEnd_7797109 := by
    simpa [prefixWord, tailWord_7797109, baseEnd_7797109] using wordTrace_append hprefix tailTrace_7797109
  have hstable : (prefixWord ++ tailWord_7797109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797109).length < 2 ^ (prefixWord ++ tailWord_7797109).sum := by decide
  have hdescent : baseEnd_7797109 < baseStart_7797109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797121 : List Nat := [1, 2, 4, 3, 1, 1, 11]
def baseStart_7797121 : Nat := 118140960795 + 7797121 * 2 ^ 59
def prefixEnd_7797121 : Nat := 4983230072969 + 3 ^ 40 * 7797121 * 2
def baseEnd_7797121 : Nat := 49428034497102388418879

theorem tailTrace_7797121 : CollatzResearch.WordTrace tailWord_7797121 prefixEnd_7797121 49428034497102388418879 := by
  unfold tailWord_7797121
  simp only [CollatzResearch.WordTrace]
  refine ⟨284384365985369734094455217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189589577323579822729636811 284384365985369734094455217)
  ·
    refine ⟨213288274489027300570841413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284384365985369734094455217 213288274489027300570841413)
    ·
      refine ⟨39991551466692618857032765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213288274489027300570841413 39991551466692618857032765)
      ·
        refine ⟨14996831800009732071387287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39991551466692618857032765 14996831800009732071387287)
        ·
          refine ⟨22495247700014598107080931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14996831800009732071387287 22495247700014598107080931)
          ·
            refine ⟨33742871550021897160621397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22495247700014598107080931 33742871550021897160621397)
            ·
              refine ⟨49428034497102388418879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33742871550021897160621397 49428034497102388418879)
              ·
                rfl

theorem cell23_7797121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 11].length) (baseStart_7797121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797121 prefixEnd_7797121 := by exact prefixLift 7797121
  have htrace : WordTrace (prefixWord ++ tailWord_7797121) baseStart_7797121 baseEnd_7797121 := by
    simpa [prefixWord, tailWord_7797121, baseEnd_7797121] using wordTrace_append hprefix tailTrace_7797121
  have hstable : (prefixWord ++ tailWord_7797121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797121).length < 2 ^ (prefixWord ++ tailWord_7797121).sum := by decide
  have hdescent : baseEnd_7797121 < baseStart_7797121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797132 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 3, 2, 2]
def baseStart_7797132 : Nat := 118140960795 + 7797132 * 2 ^ 59
def prefixEnd_7797132 : Nat := 4983230072969 + 3 ^ 40 * 7797132 * 2
def baseEnd_7797132 : Nat := 4003676442552492918891649

theorem tailTrace_7797132 : CollatzResearch.WordTrace tailWord_7797132 prefixEnd_7797132 4003676442552492918891649 := by
  unfold tailWord_7797132
  simp only [CollatzResearch.WordTrace]
  refine ⟨142192383594164941486552825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189589844792219921982070433 142192383594164941486552825)
  ·
    refine ⟨106644287695623706114914619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142192383594164941486552825 106644287695623706114914619)
    ·
      refine ⟨159966431543435559172371929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106644287695623706114914619 159966431543435559172371929)
      ·
        refine ⟨119974823657576669379278947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159966431543435559172371929 119974823657576669379278947)
        ·
          refine ⟨179962235486365004068918421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119974823657576669379278947 179962235486365004068918421)
          ·
            refine ⟨8435729788423359565730551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179962235486365004068918421 8435729788423359565730551)
            ·
              refine ⟨12653594682635039348595827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435729788423359565730551 12653594682635039348595827)
              ·
                refine ⟨18980392023952559022893741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12653594682635039348595827 18980392023952559022893741)
                ·
                  refine ⟨7117647008982209633585153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18980392023952559022893741 7117647008982209633585153)
                  ·
                    refine ⟨5338235256736657225188865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7117647008982209633585153 5338235256736657225188865)
                    ·
                      refine ⟨4003676442552492918891649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338235256736657225188865 4003676442552492918891649)
                      ·
                        rfl

theorem cell23_7797132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_7797132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797132 prefixEnd_7797132 := by exact prefixLift 7797132
  have htrace : WordTrace (prefixWord ++ tailWord_7797132) baseStart_7797132 baseEnd_7797132 := by
    simpa [prefixWord, tailWord_7797132, baseEnd_7797132] using wordTrace_append hprefix tailTrace_7797132
  have hstable : (prefixWord ++ tailWord_7797132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797132).length < 2 ^ (prefixWord ++ tailWord_7797132).sum := by decide
  have hdescent : baseEnd_7797132 < baseStart_7797132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797205 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7797205 : Nat := 118140960795 + 7797205 * 2 ^ 59
def prefixEnd_7797205 : Nat := 4983230072969 + 3 ^ 40 * 7797205 * 2
def baseEnd_7797205 : Nat := 4003713926640271133278813

theorem tailTrace_7797205 : CollatzResearch.WordTrace tailWord_7797205 prefixEnd_7797205 4003713926640271133278813 := by
  unfold tailWord_7797205
  simp only [CollatzResearch.WordTrace]
  refine ⟨284387429717065416440513069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189591619811376944293675379 284387429717065416440513069)
  ·
    refine ⟨106645286143899531165192401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284387429717065416440513069 106645286143899531165192401)
    ·
      refine ⟨79983964607924648373894301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106645286143899531165192401 79983964607924648373894301)
      ·
        refine ⟨29993986727971743140210363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79983964607924648373894301 29993986727971743140210363)
        ·
          refine ⟨44990980091957614710315545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29993986727971743140210363 44990980091957614710315545)
          ·
            refine ⟨33743235068968211032736659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44990980091957614710315545 33743235068968211032736659)
            ·
              refine ⟨50614852603452316549104989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33743235068968211032736659 50614852603452316549104989)
              ·
                refine ⟨18980569726294618705914371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50614852603452316549104989 18980569726294618705914371)
                ·
                  refine ⟨28470854589441928058871557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18980569726294618705914371 28470854589441928058871557)
                  ·
                    refine ⟨5338285235520361511038417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28470854589441928058871557 5338285235520361511038417)
                    ·
                      refine ⟨4003713926640271133278813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338285235520361511038417 4003713926640271133278813)
                      ·
                        rfl

theorem cell23_7797205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7797205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797205 prefixEnd_7797205 := by exact prefixLift 7797205
  have htrace : WordTrace (prefixWord ++ tailWord_7797205) baseStart_7797205 baseEnd_7797205 := by
    simpa [prefixWord, tailWord_7797205, baseEnd_7797205] using wordTrace_append hprefix tailTrace_7797205
  have hstable : (prefixWord ++ tailWord_7797205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797205).length < 2 ^ (prefixWord ++ tailWord_7797205).sum := by decide
  have hdescent : baseEnd_7797205 < baseStart_7797205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797251 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7]
def baseStart_7797251 : Nat := 118140960795 + 7797251 * 2 ^ 59
def prefixEnd_7797251 : Nat := 4983230072969 + 3 ^ 40 * 7797251 * 2
def baseEnd_7797251 : Nat := 4003737546750377953303601

theorem tailTrace_7797251 : CollatzResearch.WordTrace tailWord_7797251 prefixEnd_7797251 4003737546750377953303601 := by
  unfold tailWord_7797251
  simp only [CollatzResearch.WordTrace]
  refine ⟨284389107474898766296687607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189592738316599177531125071 284389107474898766296687607)
  ·
    refine ⟨426583661212348149445031411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284389107474898766296687607 426583661212348149445031411)
    ·
      refine ⟨639875491818522224167547117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426583661212348149445031411 639875491818522224167547117)
      ·
        refine ⟨239953309431945834062830169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639875491818522224167547117 239953309431945834062830169)
        ·
          refine ⟨179964982073959375547122627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239953309431945834062830169 179964982073959375547122627)
          ·
            refine ⟨269947473110939063320683941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179964982073959375547122627 269947473110939063320683941)
            ·
              refine ⟨50615151208301074372628239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269947473110939063320683941 50615151208301074372628239)
              ·
                refine ⟨75922726812451611558942359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50615151208301074372628239 75922726812451611558942359)
                ·
                  refine ⟨113884090218677417338413539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75922726812451611558942359 113884090218677417338413539)
                  ·
                    refine ⟨170826135328016126007620309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113884090218677417338413539 170826135328016126007620309)
                    ·
                      refine ⟨4003737546750377953303601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170826135328016126007620309 4003737546750377953303601)
                      ·
                        rfl

theorem cell23_7797251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_7797251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797251 prefixEnd_7797251 := by exact prefixLift 7797251
  have htrace : WordTrace (prefixWord ++ tailWord_7797251) baseStart_7797251 baseEnd_7797251 := by
    simpa [prefixWord, tailWord_7797251, baseEnd_7797251] using wordTrace_append hprefix tailTrace_7797251
  have hstable : (prefixWord ++ tailWord_7797251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797251).length < 2 ^ (prefixWord ++ tailWord_7797251).sum := by decide
  have hdescent : baseEnd_7797251 < baseStart_7797251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797291 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6]
def baseStart_7797291 : Nat := 118140960795 + 7797291 * 2 ^ 59
def prefixEnd_7797291 : Nat := 4983230072969 + 3 ^ 40 * 7797291 * 2
def baseEnd_7797291 : Nat := 4003758085976557796803417

theorem tailTrace_7797291 : CollatzResearch.WordTrace tailWord_7797291 prefixEnd_7797291 4003758085976557796803417 := by
  unfold tailWord_7797291
  simp only [CollatzResearch.WordTrace]
  refine ⟨284390566394753853128143727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189593710929835902085429151 284390566394753853128143727)
  ·
    refine ⟨426585849592130779692215591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284390566394753853128143727 426585849592130779692215591)
    ·
      refine ⟨639878774388196169538323387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426585849592130779692215591 639878774388196169538323387)
      ·
        refine ⟨959818161582294254307485081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639878774388196169538323387 959818161582294254307485081)
        ·
          refine ⟨719863621186720690730613811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959818161582294254307485081 719863621186720690730613811)
          ·
            refine ⟨1079795431780081036095920717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719863621186720690730613811 1079795431780081036095920717)
            ·
              refine ⟨404923286917530388535970269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1079795431780081036095920717 404923286917530388535970269)
              ·
                refine ⟨151846232594073895700988851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404923286917530388535970269 151846232594073895700988851)
                ·
                  refine ⟨227769348891110843551483277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151846232594073895700988851 227769348891110843551483277)
                  ·
                    refine ⟨85413505834166566331806229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227769348891110843551483277 85413505834166566331806229)
                    ·
                      refine ⟨4003758085976557796803417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85413505834166566331806229 4003758085976557796803417)
                      ·
                        rfl

theorem cell23_7797291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_7797291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797291 prefixEnd_7797291 := by exact prefixLift 7797291
  have htrace : WordTrace (prefixWord ++ tailWord_7797291) baseStart_7797291 baseEnd_7797291 := by
    simpa [prefixWord, tailWord_7797291, baseEnd_7797291] using wordTrace_append hprefix tailTrace_7797291
  have hstable : (prefixWord ++ tailWord_7797291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797291).length < 2 ^ (prefixWord ++ tailWord_7797291).sum := by decide
  have hdescent : baseEnd_7797291 < baseStart_7797291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797332 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_7797332 : Nat := 118140960795 + 7797332 * 2 ^ 59
def prefixEnd_7797332 : Nat := 4983230072969 + 3 ^ 40 * 7797332 * 2
def baseEnd_7797332 : Nat := 4003779138683392136390729

theorem tailTrace_7797332 : CollatzResearch.WordTrace tailWord_7797332 prefixEnd_7797332 4003779138683392136390729 := by
  unfold tailWord_7797332
  simp only [CollatzResearch.WordTrace]
  refine ⟨142196030893802658565193125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189594707858403544753590833 142196030893802658565193125)
  ·
    refine ⟨26661755792587998480973711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142196030893802658565193125 26661755792587998480973711)
    ·
      refine ⟨39992633688881997721460567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26661755792587998480973711 39992633688881997721460567)
      ·
        refine ⟨59988950533322996582190851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39992633688881997721460567 59988950533322996582190851)
        ·
          refine ⟨89983425799984494873286277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59988950533322996582190851 89983425799984494873286277)
          ·
            refine ⟨16871892337497092788741177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89983425799984494873286277 16871892337497092788741177)
            ·
              refine ⟨12653919253122819591555883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16871892337497092788741177 12653919253122819591555883)
              ·
                refine ⟨18980878879684229387333825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12653919253122819591555883 18980878879684229387333825)
                ·
                  refine ⟨14235659159763172040500369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18980878879684229387333825 14235659159763172040500369)
                  ·
                    refine ⟨10676744369822379030375277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14235659159763172040500369 10676744369822379030375277)
                    ·
                      refine ⟨4003779138683392136390729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10676744369822379030375277 4003779138683392136390729)
                      ·
                        rfl

theorem cell23_7797332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_7797332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797332 prefixEnd_7797332 := by exact prefixLift 7797332
  have htrace : WordTrace (prefixWord ++ tailWord_7797332) baseStart_7797332 baseEnd_7797332 := by
    simpa [prefixWord, tailWord_7797332, baseEnd_7797332] using wordTrace_append hprefix tailTrace_7797332
  have hstable : (prefixWord ++ tailWord_7797332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797332).length < 2 ^ (prefixWord ++ tailWord_7797332).sum := by decide
  have hdescent : baseEnd_7797332 < baseStart_7797332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797352 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 6]
def baseStart_7797352 : Nat := 118140960795 + 7797352 * 2 ^ 59
def prefixEnd_7797352 : Nat := 4983230072969 + 3 ^ 40 * 7797352 * 2
def baseEnd_7797352 : Nat := 444865489810720228682293

theorem tailTrace_7797352 : CollatzResearch.WordTrace tailWord_7797352 prefixEnd_7797352 444865489810720228682293 := by
  unfold tailWord_7797352
  simp only [CollatzResearch.WordTrace]
  refine ⟨142196395623766430273057155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189595194165021907030742873 142196395623766430273057155)
  ·
    refine ⟨213294593435649645409585733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142196395623766430273057155 213294593435649645409585733)
    ·
      refine ⟨39992736269184308514297325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213294593435649645409585733 39992736269184308514297325)
      ·
        refine ⟨14997276100944115692861497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39992736269184308514297325 14997276100944115692861497)
        ·
          refine ⟨11247957075708086769646123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14997276100944115692861497 11247957075708086769646123)
          ·
            refine ⟨16871935613562130154469185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11247957075708086769646123 16871935613562130154469185)
            ·
              refine ⟨12653951710171597615851889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16871935613562130154469185 12653951710171597615851889)
              ·
                refine ⟨9490463782628698211888917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12653951710171597615851889 9490463782628698211888917)
                ·
                  refine ⟨444865489810720228682293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9490463782628698211888917 444865489810720228682293)
                  ·
                    rfl

theorem cell23_7797352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 6].length) (baseStart_7797352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797352 prefixEnd_7797352 := by exact prefixLift 7797352
  have htrace : WordTrace (prefixWord ++ tailWord_7797352) baseStart_7797352 baseEnd_7797352 := by
    simpa [prefixWord, tailWord_7797352, baseEnd_7797352] using wordTrace_append hprefix tailTrace_7797352
  have hstable : (prefixWord ++ tailWord_7797352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797352).length < 2 ^ (prefixWord ++ tailWord_7797352).sum := by decide
  have hdescent : baseEnd_7797352 < baseStart_7797352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797355 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 4, 3, 2]
def baseStart_7797355 : Nat := 118140960795 + 7797355 * 2 ^ 59
def prefixEnd_7797355 : Nat := 4983230072969 + 3 ^ 40 * 7797355 * 2
def baseEnd_7797355 : Nat := 4003790948738445546403123

theorem tailTrace_7797355 : CollatzResearch.WordTrace tailWord_7797355 prefixEnd_7797355 4003790948738445546403123 := by
  unfold tailWord_7797355
  simp only [CollatzResearch.WordTrace]
  refine ⟨284392900666521992058473519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189595267111014661372315679 284392900666521992058473519)
  ·
    refine ⟨426589350999782988087710279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284392900666521992058473519 426589350999782988087710279)
    ·
      refine ⟨639884026499674482131565419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426589350999782988087710279 639884026499674482131565419)
      ·
        refine ⟨959826039749511723197348129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639884026499674482131565419 959826039749511723197348129)
        ·
          refine ⟨719869529812133792398011097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959826039749511723197348129 719869529812133792398011097)
          ·
            refine ⟨539902147359100344298508323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719869529812133792398011097 539902147359100344298508323)
            ·
              refine ⟨809853221038650516447762485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539902147359100344298508323 809853221038650516447762485)
              ·
                refine ⟨75923739472373485916977733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 809853221038650516447762485 75923739472373485916977733)
                ·
                  refine ⟨14235701151070028609433325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75923739472373485916977733 14235701151070028609433325)
                  ·
                    refine ⟨5338387931651260728537497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14235701151070028609433325 5338387931651260728537497)
                    ·
                      refine ⟨4003790948738445546403123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338387931651260728537497 4003790948738445546403123)
                      ·
                        rfl

theorem cell23_7797355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 3, 2].length) (baseStart_7797355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797355 prefixEnd_7797355 := by exact prefixLift 7797355
  have htrace : WordTrace (prefixWord ++ tailWord_7797355) baseStart_7797355 baseEnd_7797355 := by
    simpa [prefixWord, tailWord_7797355, baseEnd_7797355] using wordTrace_append hprefix tailTrace_7797355
  have hstable : (prefixWord ++ tailWord_7797355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797355).length < 2 ^ (prefixWord ++ tailWord_7797355).sum := by decide
  have hdescent : baseEnd_7797355 < baseStart_7797355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797385 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 4]
def baseStart_7797385 : Nat := 118140960795 + 7797385 * 2 ^ 59
def prefixEnd_7797385 : Nat := 4983230072969 + 3 ^ 40 * 7797385 * 2
def baseEnd_7797385 : Nat := 4003806353158080429027985

theorem tailTrace_7797385 : CollatzResearch.WordTrace tailWord_7797385 prefixEnd_7797385 4003806353158080429027985 := by
  unfold tailWord_7797385
  simp only [CollatzResearch.WordTrace]
  refine ⟨284393994856413307182065609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189595996570942204788043739 284393994856413307182065609)
  ·
    refine ⟨213295496142309980386549207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284393994856413307182065609 213295496142309980386549207)
    ·
      refine ⟨319943244213464970579823811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213295496142309980386549207 319943244213464970579823811)
      ·
        refine ⟨479914866320197455869735717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319943244213464970579823811 479914866320197455869735717)
        ·
          refine ⟨89984037435037022975575447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 479914866320197455869735717 89984037435037022975575447)
          ·
            refine ⟨134976056152555534463363171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89984037435037022975575447 134976056152555534463363171)
            ·
              refine ⟨202464084228833301695044757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134976056152555534463363171 202464084228833301695044757)
              ·
                refine ⟨9490503948226561016955223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202464084228833301695044757 9490503948226561016955223)
                ·
                  refine ⟨14235755922339841525432835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9490503948226561016955223 14235755922339841525432835)
                  ·
                    refine ⟨21353633883509762288149253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14235755922339841525432835 21353633883509762288149253)
                    ·
                      refine ⟨4003806353158080429027985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21353633883509762288149253 4003806353158080429027985)
                      ·
                        rfl

theorem cell23_7797385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_7797385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797385 prefixEnd_7797385 := by exact prefixLift 7797385
  have htrace : WordTrace (prefixWord ++ tailWord_7797385) baseStart_7797385 baseEnd_7797385 := by
    simpa [prefixWord, tailWord_7797385, baseEnd_7797385] using wordTrace_append hprefix tailTrace_7797385
  have hstable : (prefixWord ++ tailWord_7797385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797385).length < 2 ^ (prefixWord ++ tailWord_7797385).sum := by decide
  have hdescent : baseEnd_7797385 < baseStart_7797385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797388 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_7797388 : Nat := 118140960795 + 7797388 * 2 ^ 59
def prefixEnd_7797388 : Nat := 4983230072969 + 3 ^ 40 * 7797388 * 2
def baseEnd_7797388 : Nat := 4003807893600043917290471

theorem tailTrace_7797388 : CollatzResearch.WordTrace tailWord_7797388 prefixEnd_7797388 4003807893600043917290471 := by
  unfold tailWord_7797388
  simp only [CollatzResearch.WordTrace]
  refine ⟨142197052137701219347212409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189596069516934959129616545 142197052137701219347212409)
  ·
    refine ⟨106647789103275914510409307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142197052137701219347212409 106647789103275914510409307)
    ·
      refine ⟨159971683654913871765613961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106647789103275914510409307 159971683654913871765613961)
      ·
        refine ⟨119978762741185403824210471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159971683654913871765613961 119978762741185403824210471)
        ·
          refine ⟨179968144111778105736315707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119978762741185403824210471 179968144111778105736315707)
          ·
            refine ⟨269952216167667158604473561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179968144111778105736315707 269952216167667158604473561)
            ·
              refine ⟨202464162125750368953355171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269952216167667158604473561 202464162125750368953355171)
              ·
                refine ⟨303696243188625553430032757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202464162125750368953355171 303696243188625553430032757)
                ·
                  refine ⟨28471522798933645634065571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303696243188625553430032757 28471522798933645634065571)
                  ·
                    refine ⟨42707284198400468451098357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28471522798933645634065571 42707284198400468451098357)
                    ·
                      refine ⟨4003807893600043917290471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42707284198400468451098357 4003807893600043917290471)
                      ·
                        rfl

theorem cell23_7797388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_7797388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797388 prefixEnd_7797388 := by exact prefixLift 7797388
  have htrace : WordTrace (prefixWord ++ tailWord_7797388) baseStart_7797388 baseEnd_7797388 := by
    simpa [prefixWord, tailWord_7797388, baseEnd_7797388] using wordTrace_append hprefix tailTrace_7797388
  have hstable : (prefixWord ++ tailWord_7797388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797388).length < 2 ^ (prefixWord ++ tailWord_7797388).sum := by decide
  have hdescent : baseEnd_7797388 < baseStart_7797388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797396 : List Nat := [2, 4, 2, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7797396 : Nat := 118140960795 + 7797396 * 2 ^ 59
def prefixEnd_7797396 : Nat := 4983230072969 + 3 ^ 40 * 7797396 * 2
def baseEnd_7797396 : Nat := 4003812001445279885990435

theorem tailTrace_7797396 : CollatzResearch.WordTrace tailWord_7797396 prefixEnd_7797396 4003812001445279885990435 := by
  unfold tailWord_7797396
  simp only [CollatzResearch.WordTrace]
  refine ⟨142197198029686728030358021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189596264039582304040477361 142197198029686728030358021)
  ·
    refine ⟨26661974630566261505692129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142197198029686728030358021 26661974630566261505692129)
    ·
      refine ⟨19996480972924696129269097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26661974630566261505692129 19996480972924696129269097)
      ·
        refine ⟨14997360729693522096951823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19996480972924696129269097 14997360729693522096951823)
        ·
          refine ⟨22496041094540283145427735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14997360729693522096951823 22496041094540283145427735)
          ·
            refine ⟨33744061641810424718141603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22496041094540283145427735 33744061641810424718141603)
            ·
              refine ⟨50616092462715637077212405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33744061641810424718141603 50616092462715637077212405)
              ·
                refine ⟨4745258668379590975988663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50616092462715637077212405 4745258668379590975988663)
                ·
                  refine ⟨7117888002569386463982995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745258668379590975988663 7117888002569386463982995)
                  ·
                    refine ⟨10676832003854079695974493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7117888002569386463982995 10676832003854079695974493)
                    ·
                      refine ⟨4003812001445279885990435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10676832003854079695974493 4003812001445279885990435)
                      ·
                        rfl

theorem cell23_7797396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7797396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797396 prefixEnd_7797396 := by exact prefixLift 7797396
  have htrace : WordTrace (prefixWord ++ tailWord_7797396) baseStart_7797396 baseEnd_7797396 := by
    simpa [prefixWord, tailWord_7797396, baseEnd_7797396] using wordTrace_append hprefix tailTrace_7797396
  have hstable : (prefixWord ++ tailWord_7797396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797396).length < 2 ^ (prefixWord ++ tailWord_7797396).sum := by decide
  have hdescent : baseEnd_7797396 < baseStart_7797396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797422 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7797422 : Nat := 118140960795 + 7797422 * 2 ^ 59
def prefixEnd_7797422 : Nat := 4983230072969 + 3 ^ 40 * 7797422 * 2
def baseEnd_7797422 : Nat := 4003825351942296784265315

theorem tailTrace_7797422 : CollatzResearch.WordTrace tailWord_7797422 prefixEnd_7797422 4003825351942296784265315 := by
  unfold tailWord_7797422
  simp only [CollatzResearch.WordTrace]
  refine ⟨35549418044659907812645315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189596896238186175000775013 35549418044659907812645315)
  ·
    refine ⟨53324127066989861718967973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35549418044659907812645315 53324127066989861718967973)
    ·
      refine ⟨9998273825060599072306495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53324127066989861718967973 9998273825060599072306495)
      ·
        refine ⟨14997410737590898608459743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9998273825060599072306495 14997410737590898608459743)
        ·
          refine ⟨22496116106386347912689615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14997410737590898608459743 22496116106386347912689615)
          ·
            refine ⟨33744174159579521869034423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22496116106386347912689615 33744174159579521869034423)
            ·
              refine ⟨50616261239369282803551635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33744174159579521869034423 50616261239369282803551635)
              ·
                refine ⟨75924391859053924205327453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50616261239369282803551635 75924391859053924205327453)
                ·
                  refine ⟨28471646947145221576997795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75924391859053924205327453 28471646947145221576997795)
                  ·
                    refine ⟨42707470420717832365496693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28471646947145221576997795 42707470420717832365496693)
                    ·
                      refine ⟨4003825351942296784265315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42707470420717832365496693 4003825351942296784265315)
                      ·
                        rfl

theorem cell23_7797422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7797422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797422 prefixEnd_7797422 := by exact prefixLift 7797422
  have htrace : WordTrace (prefixWord ++ tailWord_7797422) baseStart_7797422 baseEnd_7797422 := by
    simpa [prefixWord, tailWord_7797422, baseEnd_7797422] using wordTrace_append hprefix tailTrace_7797422
  have hstable : (prefixWord ++ tailWord_7797422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797422).length < 2 ^ (prefixWord ++ tailWord_7797422).sum := by decide
  have hdescent : baseEnd_7797422 < baseStart_7797422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797485 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_7797485 : Nat := 118140960795 + 7797485 * 2 ^ 59
def prefixEnd_7797485 : Nat := 4983230072969 + 3 ^ 40 * 7797485 * 2
def baseEnd_7797485 : Nat := 1334619233741176679259175

theorem tailTrace_7797485 : CollatzResearch.WordTrace tailWord_7797485 prefixEnd_7797485 1334619233741176679259175 := by
  unfold tailWord_7797485
  simp only [CollatzResearch.WordTrace]
  refine ⟨284397642156051024260705909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189598428104034016173803939 284397642156051024260705909)
  ·
    refine ⟨26662278952129783524441179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284397642156051024260705909 26662278952129783524441179)
    ·
      refine ⟨39993418428194675286661769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26662278952129783524441179 39993418428194675286661769)
      ·
        refine ⟨29995063821146006464996327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39993418428194675286661769 29995063821146006464996327)
        ·
          refine ⟨44992595731719009697494491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29995063821146006464996327 44992595731719009697494491)
          ·
            refine ⟨67488893597578514546241737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44992595731719009697494491 67488893597578514546241737)
            ·
              refine ⟨50616670198183885909681303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67488893597578514546241737 50616670198183885909681303)
              ·
                refine ⟨75925005297275828864521955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50616670198183885909681303 75925005297275828864521955)
                ·
                  refine ⟨113887507945913743296782933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75925005297275828864521955 113887507945913743296782933)
                  ·
                    refine ⟨1334619233741176679259175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113887507945913743296782933 1334619233741176679259175)
                    ·
                      rfl

theorem cell23_7797485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_7797485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797485 prefixEnd_7797485 := by exact prefixLift 7797485
  have htrace : WordTrace (prefixWord ++ tailWord_7797485) baseStart_7797485 baseEnd_7797485 := by
    simpa [prefixWord, tailWord_7797485, baseEnd_7797485] using wordTrace_append hprefix tailTrace_7797485
  have hstable : (prefixWord ++ tailWord_7797485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797485).length < 2 ^ (prefixWord ++ tailWord_7797485).sum := by decide
  have hdescent : baseEnd_7797485 < baseStart_7797485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797486 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_7797486 : Nat := 118140960795 + 7797486 * 2 ^ 59
def prefixEnd_7797486 : Nat := 4983230072969 + 3 ^ 40 * 7797486 * 2
def baseEnd_7797486 : Nat := 4003858214704184533865021

theorem tailTrace_7797486 : CollatzResearch.WordTrace tailWord_7797486 prefixEnd_7797486 4003858214704184533865021 := by
  unfold tailWord_7797486
  simp only [CollatzResearch.WordTrace]
  refine ⟨35549709828630925178936539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189598452419364934287661541 35549709828630925178936539)
  ·
    refine ⟨53324564742946387768404809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35549709828630925178936539 53324564742946387768404809)
    ·
      refine ⟨39993423557209790826303607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53324564742946387768404809 39993423557209790826303607)
      ·
        refine ⟨59990135335814686239455411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39993423557209790826303607 59990135335814686239455411)
        ·
          refine ⟨89985203003722029359183117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59990135335814686239455411 89985203003722029359183117)
          ·
            refine ⟨33744451126395761009693669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89985203003722029359183117 33744451126395761009693669)
            ·
              refine ⟨6327084586199205189317563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33744451126395761009693669 6327084586199205189317563)
              ·
                refine ⟨9490626879298807783976345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327084586199205189317563 9490626879298807783976345)
                ·
                  refine ⟨7117970159474105837982259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9490626879298807783976345 7117970159474105837982259)
                  ·
                    refine ⟨10676955239211158756973389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7117970159474105837982259 10676955239211158756973389)
                    ·
                      refine ⟨4003858214704184533865021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10676955239211158756973389 4003858214704184533865021)
                      ·
                        rfl

theorem cell23_7797486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_7797486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797486 prefixEnd_7797486 := by exact prefixLift 7797486
  have htrace : WordTrace (prefixWord ++ tailWord_7797486) baseStart_7797486 baseEnd_7797486 := by
    simpa [prefixWord, tailWord_7797486, baseEnd_7797486] using wordTrace_append hprefix tailTrace_7797486
  have hstable : (prefixWord ++ tailWord_7797486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797486).length < 2 ^ (prefixWord ++ tailWord_7797486).sum := by decide
  have hdescent : baseEnd_7797486 < baseStart_7797486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797505 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_7797505 : Nat := 118140960795 + 7797505 * 2 ^ 59
def prefixEnd_7797505 : Nat := 4983230072969 + 3 ^ 40 * 7797505 * 2
def baseEnd_7797505 : Nat := 4003867970836619959527433

theorem tailTrace_7797505 : CollatzResearch.WordTrace tailWord_7797505 prefixEnd_7797505 4003867970836619959527433 := by
  unfold tailWord_7797505
  simp only [CollatzResearch.WordTrace]
  refine ⟨284398371615978567676433969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189598914410652378450955979 284398371615978567676433969)
  ·
    refine ⟨213298778711983925757325477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284398371615978567676433969 213298778711983925757325477)
    ·
      refine ⟨39993521008496986079498527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213298778711983925757325477 39993521008496986079498527)
      ·
        refine ⟨59990281512745479119247791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39993521008496986079498527 59990281512745479119247791)
        ·
          refine ⟨89985422269118218678871687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59990281512745479119247791 89985422269118218678871687)
          ·
            refine ⟨134978133403677328018307531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89985422269118218678871687 134978133403677328018307531)
            ·
              refine ⟨202467200105515992027461297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134978133403677328018307531 202467200105515992027461297)
              ·
                refine ⟨151850400079136994020595973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202467200105515992027461297 151850400079136994020595973)
                ·
                  refine ⟨28471950014838186378861745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151850400079136994020595973 28471950014838186378861745)
                  ·
                    refine ⟨21353962511128639784146309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28471950014838186378861745 21353962511128639784146309)
                    ·
                      refine ⟨4003867970836619959527433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21353962511128639784146309 4003867970836619959527433)
                      ·
                        rfl

theorem cell23_7797505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_7797505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797505 prefixEnd_7797505 := by exact prefixLift 7797505
  have htrace : WordTrace (prefixWord ++ tailWord_7797505) baseStart_7797505 baseEnd_7797505 := by
    simpa [prefixWord, tailWord_7797505, baseEnd_7797505] using wordTrace_append hprefix tailTrace_7797505
  have hstable : (prefixWord ++ tailWord_7797505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797505).length < 2 ^ (prefixWord ++ tailWord_7797505).sum := by decide
  have hdescent : baseEnd_7797505 < baseStart_7797505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797562 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_7797562 : Nat := 118140960795 + 7797562 * 2 ^ 59
def prefixEnd_7797562 : Nat := 4983230072969 + 3 ^ 40 * 7797562 * 2
def baseEnd_7797562 : Nat := 1334632413077975412171557

theorem tailTrace_7797562 : CollatzResearch.WordTrace tailWord_7797562 prefixEnd_7797562 1334632413077975412171557 := by
  unfold tailWord_7797562
  simp only [CollatzResearch.WordTrace]
  refine ⟨71100112644193016602814735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189600300384514710940839293 71100112644193016602814735)
  ·
    refine ⟨106650168966289524904222103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71100112644193016602814735 106650168966289524904222103)
    ·
      refine ⟨159975253449434287356333155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106650168966289524904222103 159975253449434287356333155)
      ·
        refine ⟨239962880174151431034499733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159975253449434287356333155 239962880174151431034499733)
        ·
          refine ⟨11248260008163348329742175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239962880174151431034499733 11248260008163348329742175)
          ·
            refine ⟨16872390012245022494613263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11248260008163348329742175 16872390012245022494613263)
            ·
              refine ⟨25308585018367533741919895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16872390012245022494613263 25308585018367533741919895)
              ·
                refine ⟨37962877527551300612879843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25308585018367533741919895 37962877527551300612879843)
                ·
                  refine ⟨56944316291326950919319765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37962877527551300612879843 56944316291326950919319765)
                  ·
                    refine ⟨1334632413077975412171557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56944316291326950919319765 1334632413077975412171557)
                    ·
                      rfl

theorem cell23_7797562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_7797562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797562 prefixEnd_7797562 := by exact prefixLift 7797562
  have htrace : WordTrace (prefixWord ++ tailWord_7797562) baseStart_7797562 baseEnd_7797562 := by
    simpa [prefixWord, tailWord_7797562, baseEnd_7797562] using wordTrace_append hprefix tailTrace_7797562
  have hstable : (prefixWord ++ tailWord_7797562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797562).length < 2 ^ (prefixWord ++ tailWord_7797562).sum := by decide
  have hdescent : baseEnd_7797562 < baseStart_7797562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797566 : List Nat := [4, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_7797566 : Nat := 118140960795 + 7797566 * 2 ^ 59
def prefixEnd_7797566 : Nat := 4983230072969 + 3 ^ 40 * 7797566 * 2
def baseEnd_7797566 : Nat := 444877699239616024540517

theorem tailTrace_7797566 : CollatzResearch.WordTrace tailWord_7797566 prefixEnd_7797566 444877699239616024540517 := by
  unfold tailWord_7797566
  simp only [CollatzResearch.WordTrace]
  refine ⟨35550074558594696886800569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189600397645838383396269701 35550074558594696886800569)
  ·
    refine ⟨26662555918946022665100427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35550074558594696886800569 26662555918946022665100427)
    ·
      refine ⟨39993833878419033997650641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26662555918946022665100427 39993833878419033997650641)
      ·
        refine ⟨29995375408814275498237981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39993833878419033997650641 29995375408814275498237981)
        ·
          refine ⟨11248265778305353311839243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29995375408814275498237981 11248265778305353311839243)
          ·
            refine ⟨16872398667458029967758865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11248265778305353311839243 16872398667458029967758865)
            ·
              refine ⟨12654299000593522475819149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16872398667458029967758865 12654299000593522475819149)
              ·
                refine ⟨4745362125222570928432181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12654299000593522475819149 4745362125222570928432181)
                ·
                  refine ⟨444877699239616024540517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4745362125222570928432181 444877699239616024540517)
                  ·
                    rfl

theorem cell23_7797566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_7797566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797566 prefixEnd_7797566 := by exact prefixLift 7797566
  have htrace : WordTrace (prefixWord ++ tailWord_7797566) baseStart_7797566 baseEnd_7797566 := by
    simpa [prefixWord, tailWord_7797566, baseEnd_7797566] using wordTrace_append hprefix tailTrace_7797566
  have hstable : (prefixWord ++ tailWord_7797566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797566).length < 2 ^ (prefixWord ++ tailWord_7797566).sum := by decide
  have hdescent : baseEnd_7797566 < baseStart_7797566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797582 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_7797582 : Nat := 118140960795 + 7797582 * 2 ^ 59
def prefixEnd_7797582 : Nat := 4983230072969 + 3 ^ 40 * 7797582 * 2
def baseEnd_7797582 : Nat := 4003907508847016158264579

theorem tailTrace_7797582 : CollatzResearch.WordTrace tailWord_7797582 prefixEnd_7797582 4003907508847016158264579 := by
  unfold tailWord_7797582
  simp only [CollatzResearch.WordTrace]
  refine ⟨35550147504587451228373375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189600786691133073217991333 35550147504587451228373375)
  ·
    refine ⟨53325221256881176842560063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35550147504587451228373375 53325221256881176842560063)
    ·
      refine ⟨79987831885321765263840095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53325221256881176842560063 79987831885321765263840095)
      ·
        refine ⟨119981747827982647895760143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79987831885321765263840095 119981747827982647895760143)
        ·
          refine ⟨179972621741973971843640215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119981747827982647895760143 179972621741973971843640215)
          ·
            refine ⟨269958932612960957765460323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179972621741973971843640215 269958932612960957765460323)
            ·
              refine ⟨404938398919441436648190485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269958932612960957765460323 404938398919441436648190485)
              ·
                refine ⟨18981487449348817342883929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 404938398919441436648190485 18981487449348817342883929)
                ·
                  refine ⟨14236115587011613007162947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18981487449348817342883929 14236115587011613007162947)
                  ·
                    refine ⟨21354173380517419510744421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14236115587011613007162947 21354173380517419510744421)
                    ·
                      refine ⟨4003907508847016158264579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21354173380517419510744421 4003907508847016158264579)
                      ·
                        rfl

theorem cell23_7797582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_7797582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797582 prefixEnd_7797582 := by exact prefixLift 7797582
  have htrace : WordTrace (prefixWord ++ tailWord_7797582) baseStart_7797582 baseEnd_7797582 := by
    simpa [prefixWord, tailWord_7797582, baseEnd_7797582] using wordTrace_append hprefix tailTrace_7797582
  have hstable : (prefixWord ++ tailWord_7797582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797582).length < 2 ^ (prefixWord ++ tailWord_7797582).sum := by decide
  have hdescent : baseEnd_7797582 < baseStart_7797582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797706 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_7797706 : Nat := 118140960795 + 7797706 * 2 ^ 59
def prefixEnd_7797706 : Nat := 4983230072969 + 3 ^ 40 * 7797706 * 2
def baseEnd_7797706 : Nat := 4003971180448173673114009

theorem tailTrace_7797706 : CollatzResearch.WordTrace tailWord_7797706 prefixEnd_7797706 4003971180448173673114009 := by
  unfold tailWord_7797706
  simp only [CollatzResearch.WordTrace]
  refine ⟨71101425672062594751125243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189603801792166919336333981 71101425672062594751125243)
  ·
    refine ⟨106652138508093892126687865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71101425672062594751125243 106652138508093892126687865)
    ·
      refine ⟨79989103881070419095015899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106652138508093892126687865 79989103881070419095015899)
      ·
        refine ⟨119983655821605628642523849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79989103881070419095015899 119983655821605628642523849)
        ·
          refine ⟨89987741866204221481892887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119983655821605628642523849 89987741866204221481892887)
          ·
            refine ⟨134981612799306332222839331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89987741866204221481892887 134981612799306332222839331)
            ·
              refine ⟨202472419198959498334258997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134981612799306332222839331 202472419198959498334258997)
              ·
                refine ⟨18981789299902452968836781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202472419198959498334258997 18981789299902452968836781)
                ·
                  refine ⟨7118170987463419863313793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18981789299902452968836781 7118170987463419863313793)
                  ·
                    refine ⟨5338628240597564897485345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7118170987463419863313793 5338628240597564897485345)
                    ·
                      refine ⟨4003971180448173673114009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338628240597564897485345 4003971180448173673114009)
                      ·
                        rfl

theorem cell23_7797706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_7797706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797706 prefixEnd_7797706 := by exact prefixLift 7797706
  have htrace : WordTrace (prefixWord ++ tailWord_7797706) baseStart_7797706 baseEnd_7797706 := by
    simpa [prefixWord, tailWord_7797706, baseEnd_7797706] using wordTrace_append hprefix tailTrace_7797706
  have hstable : (prefixWord ++ tailWord_7797706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797706).length < 2 ^ (prefixWord ++ tailWord_7797706).sum := by decide
  have hdescent : baseEnd_7797706 < baseStart_7797706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797716 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_7797716 : Nat := 118140960795 + 7797716 * 2 ^ 59
def prefixEnd_7797716 : Nat := 4983230072969 + 3 ^ 40 * 7797716 * 2
def baseEnd_7797716 : Nat := 1334658771751572877996321

theorem tailTrace_7797716 : CollatzResearch.WordTrace tailWord_7797716 prefixEnd_7797716 1334658771751572877996321 := by
  unfold tailWord_7797716
  simp only [CollatzResearch.WordTrace]
  refine ⟨142203033709107075356182501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189604044945476100474910001 142203033709107075356182501)
  ·
    refine ⟨26663068820457576629284219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142203033709107075356182501 26663068820457576629284219)
    ·
      refine ⟨39994603230686364943926329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26663068820457576629284219 39994603230686364943926329)
      ·
        refine ⟨29995952423014773707944747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39994603230686364943926329 29995952423014773707944747)
        ·
          refine ⟨44993928634522160561917121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29995952423014773707944747 44993928634522160561917121)
          ·
            refine ⟨33745446475891620421437841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44993928634522160561917121 33745446475891620421437841)
            ·
              refine ⟨25309084856918715316078381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33745446475891620421437841 25309084856918715316078381)
              ·
                refine ⟨9490906821344518243529393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25309084856918715316078381 9490906821344518243529393)
                ·
                  refine ⟨7118180116008388682647045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9490906821344518243529393 7118180116008388682647045)
                  ·
                    refine ⟨1334658771751572877996321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7118180116008388682647045 1334658771751572877996321)
                    ·
                      rfl

theorem cell23_7797716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_7797716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797716 prefixEnd_7797716 := by exact prefixLift 7797716
  have htrace : WordTrace (prefixWord ++ tailWord_7797716) baseStart_7797716 baseEnd_7797716 := by
    simpa [prefixWord, tailWord_7797716, baseEnd_7797716] using wordTrace_append hprefix tailTrace_7797716
  have hstable : (prefixWord ++ tailWord_7797716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797716).length < 2 ^ (prefixWord ++ tailWord_7797716).sum := by decide
  have hdescent : baseEnd_7797716 < baseStart_7797716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797743 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 1, 2, 3]
def baseStart_7797743 : Nat := 118140960795 + 7797743 * 2 ^ 59
def prefixEnd_7797743 : Nat := 4983230072969 + 3 ^ 40 * 7797743 * 2
def baseEnd_7797743 : Nat := 4003990179232390028351339

theorem tailTrace_7797743 : CollatzResearch.WordTrace tailWord_7797743 prefixEnd_7797743 4003990179232390028351339 := by
  unfold tailWord_7797743
  simp only [CollatzResearch.WordTrace]
  refine ⟨284407052189116334323597883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189604701459410889549065255 284407052189116334323597883)
  ·
    refine ⟨426610578283674501485396825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284407052189116334323597883 426610578283674501485396825)
    ·
      refine ⟨319957933712755876114047619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426610578283674501485396825 319957933712755876114047619)
      ·
        refine ⟨479936900569133814171071429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319957933712755876114047619 479936900569133814171071429)
        ·
          refine ⟨89988168856712590157075893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 479936900569133814171071429 89988168856712590157075893)
          ·
            refine ⟨8436390830316805327225865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89988168856712590157075893 8436390830316805327225865)
            ·
              refine ⟨6327293122737603995419399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8436390830316805327225865 6327293122737603995419399)
              ·
                refine ⟨9490939684106405993129099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327293122737603995419399 9490939684106405993129099)
                ·
                  refine ⟨14236409526159608989693649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9490939684106405993129099 14236409526159608989693649)
                  ·
                    refine ⟨10677307144619706742270237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14236409526159608989693649 10677307144619706742270237)
                    ·
                      refine ⟨4003990179232390028351339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10677307144619706742270237 4003990179232390028351339)
                      ·
                        rfl

theorem cell23_7797743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 2, 3].length) (baseStart_7797743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797743 prefixEnd_7797743 := by exact prefixLift 7797743
  have htrace : WordTrace (prefixWord ++ tailWord_7797743) baseStart_7797743 baseEnd_7797743 := by
    simpa [prefixWord, tailWord_7797743, baseEnd_7797743] using wordTrace_append hprefix tailTrace_7797743
  have hstable : (prefixWord ++ tailWord_7797743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797743).length < 2 ^ (prefixWord ++ tailWord_7797743).sum := by decide
  have hdescent : baseEnd_7797743 < baseStart_7797743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797756 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_7797756 : Nat := 118140960795 + 7797756 * 2 ^ 59
def prefixEnd_7797756 : Nat := 4983230072969 + 3 ^ 40 * 7797756 * 2
def baseEnd_7797756 : Nat := 4003996854480898477488779

theorem tailTrace_7797756 : CollatzResearch.WordTrace tailWord_7797756 prefixEnd_7797756 4003996854480898477488779 := by
  unfold tailWord_7797756
  simp only [CollatzResearch.WordTrace]
  refine ⟨142203763169034618771910561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189605017558712825029214081 142203763169034618771910561)
  ·
    refine ⟨106652822376775964078932921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142203763169034618771910561 106652822376775964078932921)
    ·
      refine ⟨79989616782581973059199691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106652822376775964078932921 79989616782581973059199691)
      ·
        refine ⟨119984425173872959588799537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79989616782581973059199691 119984425173872959588799537)
        ·
          refine ⟨89988318880404719691599653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119984425173872959588799537 89988318880404719691599653)
          ·
            refine ⟨16872809790075884942174935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89988318880404719691599653 16872809790075884942174935)
            ·
              refine ⟨25309214685113827413262403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16872809790075884942174935 25309214685113827413262403)
              ·
                refine ⟨37963822027670741119893605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25309214685113827413262403 37963822027670741119893605)
                ·
                  refine ⟨7118216630188263959980051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37963822027670741119893605 7118216630188263959980051)
                  ·
                    refine ⟨10677324945282395939970077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7118216630188263959980051 10677324945282395939970077)
                    ·
                      refine ⟨4003996854480898477488779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10677324945282395939970077 4003996854480898477488779)
                      ·
                        rfl

theorem cell23_7797756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_7797756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797756 prefixEnd_7797756 := by exact prefixLift 7797756
  have htrace : WordTrace (prefixWord ++ tailWord_7797756) baseStart_7797756 baseEnd_7797756 := by
    simpa [prefixWord, tailWord_7797756, baseEnd_7797756] using wordTrace_append hprefix tailTrace_7797756
  have hstable : (prefixWord ++ tailWord_7797756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797756).length < 2 ^ (prefixWord ++ tailWord_7797756).sum := by decide
  have hdescent : baseEnd_7797756 < baseStart_7797756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797783 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7797783 : Nat := 118140960795 + 7797783 * 2 ^ 59
def prefixEnd_7797783 : Nat := 4983230072969 + 3 ^ 40 * 7797783 * 2
def baseEnd_7797783 : Nat := 4004010718458569871851155

theorem tailTrace_7797783 : CollatzResearch.WordTrace tailWord_7797783 prefixEnd_7797783 4004010718458569871851155 := by
  unfold tailWord_7797783
  simp only [CollatzResearch.WordTrace]
  refine ⟨284408511108971421155054003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189605674072647614103369335 284408511108971421155054003)
  ·
    refine ⟨426612766663457131732581005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284408511108971421155054003 426612766663457131732581005)
    ·
      refine ⟨159979787498796424399717877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426612766663457131732581005 159979787498796424399717877)
      ·
        refine ⟨14998105078012164787473551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159979787498796424399717877 14998105078012164787473551)
        ·
          refine ⟨22497157617018247181210327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14998105078012164787473551 22497157617018247181210327)
          ·
            refine ⟨33745736425527370771815491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22497157617018247181210327 33745736425527370771815491)
            ·
              refine ⟨50618604638291056157723237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33745736425527370771815491 50618604638291056157723237)
              ·
                refine ⟨9490988369679573029573107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50618604638291056157723237 9490988369679573029573107)
                ·
                  refine ⟨14236482554519359544359661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9490988369679573029573107 14236482554519359544359661)
                  ·
                    refine ⟨5338680957944759829134873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14236482554519359544359661 5338680957944759829134873)
                    ·
                      refine ⟨4004010718458569871851155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338680957944759829134873 4004010718458569871851155)
                      ·
                        rfl

theorem cell23_7797783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7797783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797783 prefixEnd_7797783 := by exact prefixLift 7797783
  have htrace : WordTrace (prefixWord ++ tailWord_7797783) baseStart_7797783 baseEnd_7797783 := by
    simpa [prefixWord, tailWord_7797783, baseEnd_7797783] using wordTrace_append hprefix tailTrace_7797783
  have hstable : (prefixWord ++ tailWord_7797783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797783).length < 2 ^ (prefixWord ++ tailWord_7797783).sum := by decide
  have hdescent : baseEnd_7797783 < baseStart_7797783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797813 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_7797813 : Nat := 118140960795 + 7797813 * 2 ^ 59
def prefixEnd_7797813 : Nat := 4983230072969 + 3 ^ 40 * 7797813 * 2
def baseEnd_7797813 : Nat := 4004026122878204754476017

theorem tailTrace_7797813 : CollatzResearch.WordTrace tailWord_7797813 prefixEnd_7797813 4004026122878204754476017 := by
  unfold tailWord_7797813
  simp only [CollatzResearch.WordTrace]
  refine ⟨284409605298862736278646093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189606403532575157519097395 284409605298862736278646093)
  ·
    refine ⟨106653601987073526104492285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284409605298862736278646093 106653601987073526104492285)
    ·
      refine ⟨39995100745152572289184607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106653601987073526104492285 39995100745152572289184607)
      ·
        refine ⟨59992651117728858433776911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39995100745152572289184607 59992651117728858433776911)
        ·
          refine ⟨89988976676593287650665367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59992651117728858433776911 89988976676593287650665367)
          ·
            refine ⟨134983465014889931475998051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89988976676593287650665367 134983465014889931475998051)
            ·
              refine ⟨202475197522334897213997077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134983465014889931475998051 202475197522334897213997077)
              ·
                refine ⟨9491024883859448306906113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202475197522334897213997077 9491024883859448306906113)
                ·
                  refine ⟨7118268662894586230179585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491024883859448306906113 7118268662894586230179585)
                  ·
                    refine ⟨5338701497170939672634689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7118268662894586230179585 5338701497170939672634689)
                    ·
                      refine ⟨4004026122878204754476017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338701497170939672634689 4004026122878204754476017)
                      ·
                        rfl

theorem cell23_7797813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_7797813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797813 prefixEnd_7797813 := by exact prefixLift 7797813
  have htrace : WordTrace (prefixWord ++ tailWord_7797813) baseStart_7797813 baseEnd_7797813 := by
    simpa [prefixWord, tailWord_7797813, baseEnd_7797813] using wordTrace_append hprefix tailTrace_7797813
  have hstable : (prefixWord ++ tailWord_7797813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797813).length < 2 ^ (prefixWord ++ tailWord_7797813).sum := by decide
  have hdescent : baseEnd_7797813 < baseStart_7797813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797829 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_7797829 : Nat := 118140960795 + 7797829 * 2 ^ 59
def prefixEnd_7797829 : Nat := 4983230072969 + 3 ^ 40 * 7797829 * 2
def baseEnd_7797829 : Nat := 4004034338568676691875943

theorem tailTrace_7797829 : CollatzResearch.WordTrace tailWord_7797829 prefixEnd_7797829 4004034338568676691875943 := by
  unfold tailWord_7797829
  simp only [CollatzResearch.WordTrace]
  refine ⟨284410188866804771011228541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189606792577869847340819027 284410188866804771011228541)
  ·
    refine ⟨106653820825051789129210703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284410188866804771011228541 106653820825051789129210703)
    ·
      refine ⟨159980731237577683693816055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106653820825051789129210703 159980731237577683693816055)
      ·
        refine ⟨239971096856366525540724083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159980731237577683693816055 239971096856366525540724083)
        ·
          refine ⟨359956645284549788311086125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239971096856366525540724083 359956645284549788311086125)
          ·
            refine ⟨134983741981706170616657297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359956645284549788311086125 134983741981706170616657297)
            ·
              refine ⟨101237806486279627962492973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134983741981706170616657297 101237806486279627962492973)
              ·
                refine ⟨37964177432354860485934865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101237806486279627962492973 37964177432354860485934865)
                ·
                  refine ⟨28473133074266145364451149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37964177432354860485934865 28473133074266145364451149)
                  ·
                    refine ⟨10677424902849804511669181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28473133074266145364451149 10677424902849804511669181)
                    ·
                      refine ⟨4004034338568676691875943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10677424902849804511669181 4004034338568676691875943)
                      ·
                        rfl

theorem cell23_7797829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_7797829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797829 prefixEnd_7797829 := by exact prefixLift 7797829
  have htrace : WordTrace (prefixWord ++ tailWord_7797829) baseStart_7797829 baseEnd_7797829 := by
    simpa [prefixWord, tailWord_7797829, baseEnd_7797829] using wordTrace_append hprefix tailTrace_7797829
  have hstable : (prefixWord ++ tailWord_7797829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797829).length < 2 ^ (prefixWord ++ tailWord_7797829).sum := by decide
  have hdescent : baseEnd_7797829 < baseStart_7797829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797866 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_7797866 : Nat := 118140960795 + 7797866 * 2 ^ 59
def prefixEnd_7797866 : Nat := 4983230072969 + 3 ^ 40 * 7797866 * 2
def baseEnd_7797866 : Nat := 1334684445784297682371091

theorem tailTrace_7797866 : CollatzResearch.WordTrace tailWord_7797866 prefixEnd_7797866 1334684445784297682371091 := by
  unfold tailWord_7797866
  simp only [CollatzResearch.WordTrace]
  refine ⟨71102884591917681582581363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189607692245113817553550301 71102884591917681582581363)
  ·
    refine ⟨106654326887876522373872045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71102884591917681582581363 106654326887876522373872045)
    ·
      refine ⟨39995372582953695890202017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106654326887876522373872045 39995372582953695890202017)
      ·
        refine ⟨29996529437215271917651513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39995372582953695890202017 29996529437215271917651513)
        ·
          refine ⟨22497397077911453938238635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29996529437215271917651513 22497397077911453938238635)
          ·
            refine ⟨33746095616867180907357953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22497397077911453938238635 33746095616867180907357953)
            ·
              refine ⟨25309571712650385680518465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33746095616867180907357953 25309571712650385680518465)
              ·
                refine ⟨18982178784487789260388849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25309571712650385680518465 18982178784487789260388849)
                ·
                  refine ⟨14236634088365841945291637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18982178784487789260388849 14236634088365841945291637)
                  ·
                    refine ⟨1334684445784297682371091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14236634088365841945291637 1334684445784297682371091)
                    ·
                      rfl

theorem cell23_7797866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_7797866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797866 prefixEnd_7797866 := by exact prefixLift 7797866
  have htrace : WordTrace (prefixWord ++ tailWord_7797866) baseStart_7797866 baseEnd_7797866 := by
    simpa [prefixWord, tailWord_7797866, baseEnd_7797866] using wordTrace_append hprefix tailTrace_7797866
  have hstable : (prefixWord ++ tailWord_7797866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797866).length < 2 ^ (prefixWord ++ tailWord_7797866).sum := by decide
  have hdescent : baseEnd_7797866 < baseStart_7797866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797870 : List Nat := [4, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_7797870 : Nat := 118140960795 + 7797870 * 2 ^ 59
def prefixEnd_7797870 : Nat := 4983230072969 + 3 ^ 40 * 7797870 * 2
def baseEnd_7797870 : Nat := 444895043475056781273695

theorem tailTrace_7797870 : CollatzResearch.WordTrace tailWord_7797870 prefixEnd_7797870 444895043475056781273695 := by
  unfold tailWord_7797870
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551460532457029376683883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189607789506437490008980709 35551460532457029376683883)
  ·
    refine ⟨53327190798685544065025825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35551460532457029376683883 53327190798685544065025825)
    ·
      refine ⟨39995393099014158048769369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53327190798685544065025825 39995393099014158048769369)
      ·
        refine ⟨29996544824260618536577027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39995393099014158048769369 29996544824260618536577027)
        ·
          refine ⟨44994817236390927804865541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29996544824260618536577027 44994817236390927804865541)
          ·
            refine ⟨8436528231823298963412289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44994817236390927804865541 8436528231823298963412289)
            ·
              refine ⟨6327396173867474222559217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8436528231823298963412289 6327396173867474222559217)
              ·
                refine ⟨4745547130400605666919413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6327396173867474222559217 4745547130400605666919413)
                ·
                  refine ⟨444895043475056781273695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4745547130400605666919413 444895043475056781273695)
                  ·
                    rfl

theorem cell23_7797870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_7797870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797870 prefixEnd_7797870 := by exact prefixLift 7797870
  have htrace : WordTrace (prefixWord ++ tailWord_7797870) baseStart_7797870 baseEnd_7797870 := by
    simpa [prefixWord, tailWord_7797870, baseEnd_7797870] using wordTrace_append hprefix tailTrace_7797870
  have hstable : (prefixWord ++ tailWord_7797870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797870).length < 2 ^ (prefixWord ++ tailWord_7797870).sum := by decide
  have hdescent : baseEnd_7797870 < baseStart_7797870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797930 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_7797930 : Nat := 118140960795 + 7797930 * 2 ^ 59
def prefixEnd_7797930 : Nat := 4983230072969 + 3 ^ 40 * 7797930 * 2
def baseEnd_7797930 : Nat := 1334695400038260265570993

theorem tailTrace_7797930 : CollatzResearch.WordTrace tailWord_7797930 prefixEnd_7797930 1334695400038260265570993 := by
  unfold tailWord_7797930
  simp only [CollatzResearch.WordTrace]
  refine ⟨71103468159859716315163811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189609248426292576840436829 71103468159859716315163811)
  ·
    refine ⟨106655202239789574472745717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71103468159859716315163811 106655202239789574472745717)
    ·
      refine ⟨9998925209980272606819911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106655202239789574472745717 9998925209980272606819911)
      ·
        refine ⟨14998387814970408910229867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9998925209980272606819911 14998387814970408910229867)
        ·
          refine ⟨22497581722455613365344801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14998387814970408910229867 22497581722455613365344801)
          ·
            refine ⟨16873186291841710024008601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22497581722455613365344801 16873186291841710024008601)
            ·
              refine ⟨12654889718881282518006451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16873186291841710024008601 12654889718881282518006451)
              ·
                refine ⟨18982334578321923777009677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12654889718881282518006451 18982334578321923777009677)
                ·
                  refine ⟨7118375466870721416378629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18982334578321923777009677 7118375466870721416378629)
                  ·
                    refine ⟨1334695400038260265570993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7118375466870721416378629 1334695400038260265570993)
                    ·
                      rfl

theorem cell23_7797930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_7797930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797930 prefixEnd_7797930 := by exact prefixLift 7797930
  have htrace : WordTrace (prefixWord ++ tailWord_7797930) baseStart_7797930 baseEnd_7797930 := by
    simpa [prefixWord, tailWord_7797930, baseEnd_7797930] using wordTrace_append hprefix tailTrace_7797930
  have hstable : (prefixWord ++ tailWord_7797930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797930).length < 2 ^ (prefixWord ++ tailWord_7797930).sum := by decide
  have hdescent : baseEnd_7797930 < baseStart_7797930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797936 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 7, 1, 3]
def baseStart_7797936 : Nat := 118140960795 + 7797936 * 2 ^ 59
def prefixEnd_7797936 : Nat := 4983230072969 + 3 ^ 40 * 7797936 * 2
def baseEnd_7797936 : Nat := 4004089280998707773237951

theorem tailTrace_7797936 : CollatzResearch.WordTrace tailWord_7797936 prefixEnd_7797936 4004089280998707773237951 := by
  unfold tailWord_7797936
  simp only [CollatzResearch.WordTrace]
  refine ⟨142207045738708564142686831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189609394318278085523582441 142207045738708564142686831)
  ·
    refine ⟨213310568608062846214030247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142207045738708564142686831 213310568608062846214030247)
    ·
      refine ⟨319965852912094269321045371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213310568608062846214030247 319965852912094269321045371)
      ·
        refine ⟨479948779368141403981568057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319965852912094269321045371 479948779368141403981568057)
        ·
          refine ⟨359961584526106052986176043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479948779368141403981568057 359961584526106052986176043)
          ·
            refine ⟨539942376789159079479264065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359961584526106052986176043 539942376789159079479264065)
            ·
              refine ⟨404956782591869309609448049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539942376789159079479264065 404956782591869309609448049)
              ·
                refine ⟨303717586943901982207086037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404956782591869309609448049 303717586943901982207086037)
                ·
                  refine ⟨7118380943997702707978579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 303717586943901982207086037 7118380943997702707978579)
                  ·
                    refine ⟨10677571415996554061967869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7118380943997702707978579 10677571415996554061967869)
                    ·
                      refine ⟨4004089280998707773237951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10677571415996554061967869 4004089280998707773237951)
                      ·
                        rfl

theorem cell23_7797936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 7, 1, 3].length) (baseStart_7797936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797936 prefixEnd_7797936 := by exact prefixLift 7797936
  have htrace : WordTrace (prefixWord ++ tailWord_7797936) baseStart_7797936 baseEnd_7797936 := by
    simpa [prefixWord, tailWord_7797936, baseEnd_7797936] using wordTrace_append hprefix tailTrace_7797936
  have hstable : (prefixWord ++ tailWord_7797936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797936).length < 2 ^ (prefixWord ++ tailWord_7797936).sum := by decide
  have hdescent : baseEnd_7797936 < baseStart_7797936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797939 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 5, 5]
def baseStart_7797939 : Nat := 118140960795 + 7797939 * 2 ^ 59
def prefixEnd_7797939 : Nat := 4983230072969 + 3 ^ 40 * 7797939 * 2
def baseEnd_7797939 : Nat := 1334696940480223753833479

theorem tailTrace_7797939 : CollatzResearch.WordTrace tailWord_7797939 prefixEnd_7797939 1334696940480223753833479 := by
  unfold tailWord_7797939
  simp only [CollatzResearch.WordTrace]
  refine ⟨284414200896406259797732871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189609467264270839865155247 284414200896406259797732871)
  ·
    refine ⟨426621301344609389696599307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284414200896406259797732871 426621301344609389696599307)
    ·
      refine ⟨639931952016914084544898961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426621301344609389696599307 639931952016914084544898961)
      ·
        refine ⟨479948964012685563408674221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639931952016914084544898961 479948964012685563408674221)
        ·
          refine ⟨179980861504757086278252833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479948964012685563408674221 179980861504757086278252833)
          ·
            refine ⟨134985646128567814708689625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179980861504757086278252833 134985646128567814708689625)
            ·
              refine ⟨101239234596425861031517219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134985646128567814708689625 101239234596425861031517219)
              ·
                refine ⟨151858851894638791547275829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101239234596425861031517219 151858851894638791547275829)
                ·
                  refine ⟨14236767365122386707557109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151858851894638791547275829 14236767365122386707557109)
                  ·
                    refine ⟨1334696940480223753833479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14236767365122386707557109 1334696940480223753833479)
                    ·
                      rfl

theorem cell23_7797939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 5].length) (baseStart_7797939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797939 prefixEnd_7797939 := by exact prefixLift 7797939
  have htrace : WordTrace (prefixWord ++ tailWord_7797939) baseStart_7797939 baseEnd_7797939 := by
    simpa [prefixWord, tailWord_7797939, baseEnd_7797939] using wordTrace_append hprefix tailTrace_7797939
  have hstable : (prefixWord ++ tailWord_7797939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797939).length < 2 ^ (prefixWord ++ tailWord_7797939).sum := by decide
  have hdescent : baseEnd_7797939 < baseStart_7797939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797949 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7797949 : Nat := 118140960795 + 7797949 * 2 ^ 59
def prefixEnd_7797949 : Nat := 4983230072969 + 3 ^ 40 * 7797949 * 2
def baseEnd_7797949 : Nat := 4004095956247216222375391

theorem tailTrace_7797949 : CollatzResearch.WordTrace tailWord_7797949 prefixEnd_7797949 4004095956247216222375391 := by
  unfold tailWord_7797949
  simp only [CollatzResearch.WordTrace]
  refine ⟨284414565626370031505596901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189609710417580021003731267 284414565626370031505596901)
  ·
    refine ⟨53327731054944380907299419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284414565626370031505596901 53327731054944380907299419)
    ·
      refine ⟨79991596582416571360949129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53327731054944380907299419 79991596582416571360949129)
      ·
        refine ⟨59993697436812428520711847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79991596582416571360949129 59993697436812428520711847)
        ·
          refine ⟨89990546155218642781067771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59993697436812428520711847 89990546155218642781067771)
          ·
            refine ⟨134985819232827964171601657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89990546155218642781067771 134985819232827964171601657)
            ·
              refine ⟨101239364424620973128701243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134985819232827964171601657 101239364424620973128701243)
              ·
                refine ⟨151859046636931459693051865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101239364424620973128701243 151859046636931459693051865)
                ·
                  refine ⟨113894284977698594769788899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151859046636931459693051865 113894284977698594769788899)
                  ·
                    refine ⟨170841427466547892154683349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113894284977698594769788899 170841427466547892154683349)
                    ·
                      refine ⟨4004095956247216222375391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170841427466547892154683349 4004095956247216222375391)
                      ·
                        rfl

theorem cell23_7797949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7797949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797949 prefixEnd_7797949 := by exact prefixLift 7797949
  have htrace : WordTrace (prefixWord ++ tailWord_7797949) baseStart_7797949 baseEnd_7797949 := by
    simpa [prefixWord, tailWord_7797949, baseEnd_7797949] using wordTrace_append hprefix tailTrace_7797949
  have hstable : (prefixWord ++ tailWord_7797949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797949).length < 2 ^ (prefixWord ++ tailWord_7797949).sum := by decide
  have hdescent : baseEnd_7797949 < baseStart_7797949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797959 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_7797959 : Nat := 118140960795 + 7797959 * 2 ^ 59
def prefixEnd_7797959 : Nat := 4983230072969 + 3 ^ 40 * 7797959 * 2
def baseEnd_7797959 : Nat := 4004101091053761183250345

theorem tailTrace_7797959 : CollatzResearch.WordTrace tailWord_7797959 prefixEnd_7797959 4004101091053761183250345 := by
  unfold tailWord_7797959
  simp only [CollatzResearch.WordTrace]
  refine ⟨284414930356333803213460931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189609953570889202142307287 284414930356333803213460931)
  ·
    refine ⟨426622395534500704820191397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284414930356333803213460931 426622395534500704820191397)
    ·
      refine ⟨79991699162718882153785887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426622395534500704820191397 79991699162718882153785887)
      ·
        refine ⟨119987548744078323230678831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79991699162718882153785887 119987548744078323230678831)
        ·
          refine ⟨179981323116117484846018247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119987548744078323230678831 179981323116117484846018247)
          ·
            refine ⟨269971984674176227269027371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179981323116117484846018247 269971984674176227269027371)
            ·
              refine ⟨404957977011264340903541057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269971984674176227269027371 404957977011264340903541057)
              ·
                refine ⟨303718482758448255677655793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404957977011264340903541057 303718482758448255677655793)
                ·
                  refine ⟨227788862068836191758241845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303718482758448255677655793 227788862068836191758241845)
                  ·
                    refine ⟨21355205818953392977335173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 227788862068836191758241845 21355205818953392977335173)
                    ·
                      refine ⟨4004101091053761183250345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21355205818953392977335173 4004101091053761183250345)
                      ·
                        rfl

theorem cell23_7797959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_7797959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797959 prefixEnd_7797959 := by exact prefixLift 7797959
  have htrace : WordTrace (prefixWord ++ tailWord_7797959) baseStart_7797959 baseEnd_7797959 := by
    simpa [prefixWord, tailWord_7797959, baseEnd_7797959] using wordTrace_append hprefix tailTrace_7797959
  have hstable : (prefixWord ++ tailWord_7797959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797959).length < 2 ^ (prefixWord ++ tailWord_7797959).sum := by decide
  have hdescent : baseEnd_7797959 < baseStart_7797959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797969 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 3, 6]
def baseStart_7797969 : Nat := 118140960795 + 7797969 * 2 ^ 59
def prefixEnd_7797969 : Nat := 4983230072969 + 3 ^ 40 * 7797969 * 2
def baseEnd_7797969 : Nat := 1334702075286768714708433

theorem tailTrace_7797969 : CollatzResearch.WordTrace tailWord_7797969 prefixEnd_7797969 1334702075286768714708433 := by
  unfold tailWord_7797969
  simp only [CollatzResearch.WordTrace]
  refine ⟨284415295086297574921324961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189610196724198383280883307 284415295086297574921324961)
  ·
    refine ⟨213311471314723181190993721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284415295086297574921324961 213311471314723181190993721)
    ·
      refine ⟨159983603486042385893245291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213311471314723181190993721 159983603486042385893245291)
      ·
        refine ⟨239975405229063578839867937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159983603486042385893245291 239975405229063578839867937)
        ·
          refine ⟨179981553921797684129900953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239975405229063578839867937 179981553921797684129900953)
          ·
            refine ⟨134986165441348263097425715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179981553921797684129900953 134986165441348263097425715)
            ·
              refine ⟨202479248162022394646138573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134986165441348263097425715 202479248162022394646138573)
              ·
                refine ⟨75929718060758397992301965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202479248162022394646138573 75929718060758397992301965)
                ·
                  refine ⟨28473644272784399247113237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75929718060758397992301965 28473644272784399247113237)
                  ·
                    refine ⟨1334702075286768714708433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28473644272784399247113237 1334702075286768714708433)
                    ·
                      rfl

theorem cell23_7797969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_7797969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797969 prefixEnd_7797969 := by exact prefixLift 7797969
  have htrace : WordTrace (prefixWord ++ tailWord_7797969) baseStart_7797969 baseEnd_7797969 := by
    simpa [prefixWord, tailWord_7797969, baseEnd_7797969] using wordTrace_append hprefix tailTrace_7797969
  have hstable : (prefixWord ++ tailWord_7797969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797969).length < 2 ^ (prefixWord ++ tailWord_7797969).sum := by decide
  have hdescent : baseEnd_7797969 < baseStart_7797969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797973 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_7797973 : Nat := 118140960795 + 7797973 * 2 ^ 59
def prefixEnd_7797973 : Nat := 4983230072969 + 3 ^ 40 * 7797973 * 2
def baseEnd_7797973 : Nat := 1334702759927641376158427

theorem tailTrace_7797973 : CollatzResearch.WordTrace tailWord_7797973 prefixEnd_7797973 1334702759927641376158427 := by
  unfold tailWord_7797973
  simp only [CollatzResearch.WordTrace]
  refine ⟨284415440978283083604470573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189610293985522055736313715 284415440978283083604470573)
  ·
    refine ⟨106655790366856156351676465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284415440978283083604470573 106655790366856156351676465)
    ·
      refine ⟨79991842775142117263757349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106655790366856156351676465 79991842775142117263757349)
      ·
        refine ⟨14998470520339146986954503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79991842775142117263757349 14998470520339146986954503)
        ·
          refine ⟨22497705780508720480431755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14998470520339146986954503 22497705780508720480431755)
          ·
            refine ⟨33746558670763080720647633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22497705780508720480431755 33746558670763080720647633)
            ·
              refine ⟨25309919003072310540485725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33746558670763080720647633 25309919003072310540485725)
              ·
                refine ⟨9491219626152116452682147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25309919003072310540485725 9491219626152116452682147)
                ·
                  refine ⟨14236829439228174679023221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9491219626152116452682147 14236829439228174679023221)
                  ·
                    refine ⟨1334702759927641376158427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14236829439228174679023221 1334702759927641376158427)
                    ·
                      rfl

theorem cell23_7797973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_7797973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797973 prefixEnd_7797973 := by exact prefixLift 7797973
  have htrace : WordTrace (prefixWord ++ tailWord_7797973) baseStart_7797973 baseEnd_7797973 := by
    simpa [prefixWord, tailWord_7797973, baseEnd_7797973] using wordTrace_append hprefix tailTrace_7797973
  have hstable : (prefixWord ++ tailWord_7797973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797973).length < 2 ^ (prefixWord ++ tailWord_7797973).sum := by decide
  have hdescent : baseEnd_7797973 < baseStart_7797973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7797996 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_7797996 : Nat := 118140960795 + 7797996 * 2 ^ 59
def prefixEnd_7797996 : Nat := 4983230072969 + 3 ^ 40 * 7797996 * 2
def baseEnd_7797996 : Nat := 4004120089837977538487675

theorem tailTrace_7797996 : CollatzResearch.WordTrace tailWord_7797996 prefixEnd_7797996 4004120089837977538487675 := by
  unfold tailWord_7797996
  simp only [CollatzResearch.WordTrace]
  refine ⟨142208139928599879266278921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189610853238133172355038561 142208139928599879266278921)
  ·
    refine ⟨106656104946449909449709191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142208139928599879266278921 106656104946449909449709191)
    ·
      refine ⟨159984157419674864174563787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106656104946449909449709191 159984157419674864174563787)
      ·
        refine ⟨239976236129512296261845681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159984157419674864174563787 239976236129512296261845681)
        ·
          refine ⟨179982177097134222196384261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239976236129512296261845681 179982177097134222196384261)
          ·
            refine ⟨33746658205712666661822049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179982177097134222196384261 33746658205712666661822049)
            ·
              refine ⟨25309993654284499996366537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33746658205712666661822049 25309993654284499996366537)
              ·
                refine ⟨18982495240713374997274903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25309993654284499996366537 18982495240713374997274903)
                ·
                  refine ⟨28473742861070062495912355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18982495240713374997274903 28473742861070062495912355)
                  ·
                    refine ⟨42710614291605093743868533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28473742861070062495912355 42710614291605093743868533)
                    ·
                      refine ⟨4004120089837977538487675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42710614291605093743868533 4004120089837977538487675)
                      ·
                        rfl

theorem cell23_7797996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_7797996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7797996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7797996 prefixEnd_7797996 := by exact prefixLift 7797996
  have htrace : WordTrace (prefixWord ++ tailWord_7797996) baseStart_7797996 baseEnd_7797996 := by
    simpa [prefixWord, tailWord_7797996, baseEnd_7797996] using wordTrace_append hprefix tailTrace_7797996
  have hstable : (prefixWord ++ tailWord_7797996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7797996).length < 2 ^ (prefixWord ++ tailWord_7797996).sum := by decide
  have hdescent : baseEnd_7797996 < baseStart_7797996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7797996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798003 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 2, 4]
def baseStart_7798003 : Nat := 118140960795 + 7798003 * 2 ^ 59
def prefixEnd_7798003 : Nat := 4983230072969 + 3 ^ 40 * 7798003 * 2
def baseEnd_7798003 : Nat := 1334707894734186337033381

theorem tailTrace_7798003 : CollatzResearch.WordTrace tailWord_7798003 prefixEnd_7798003 1334707894734186337033381 := by
  unfold tailWord_7798003
  simp only [CollatzResearch.WordTrace]
  refine ⟨284416535168174398728062663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189611023445449599152041775 284416535168174398728062663)
  ·
    refine ⟨426624802752261598092093995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284416535168174398728062663 426624802752261598092093995)
    ·
      refine ⟨639937204128392397138140993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426624802752261598092093995 639937204128392397138140993)
      ·
        refine ⟨479952903096294297853605745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639937204128392397138140993 479952903096294297853605745)
        ·
          refine ⟨359964677322220723390204309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479952903096294297853605745 359964677322220723390204309)
          ·
            refine ⟨16873344249479096408915827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 359964677322220723390204309 16873344249479096408915827)
            ·
              refine ⟨25310016374218644613373741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16873344249479096408915827 25310016374218644613373741)
              ·
                refine ⟨9491256140331991730015153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25310016374218644613373741 9491256140331991730015153)
                ·
                  refine ⟨7118442105248993797511365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491256140331991730015153 7118442105248993797511365)
                  ·
                    refine ⟨1334707894734186337033381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7118442105248993797511365 1334707894734186337033381)
                    ·
                      rfl

theorem cell23_7798003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 4].length) (baseStart_7798003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798003 prefixEnd_7798003 := by exact prefixLift 7798003
  have htrace : WordTrace (prefixWord ++ tailWord_7798003) baseStart_7798003 baseEnd_7798003 := by
    simpa [prefixWord, tailWord_7798003, baseEnd_7798003] using wordTrace_append hprefix tailTrace_7798003
  have hstable : (prefixWord ++ tailWord_7798003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798003).length < 2 ^ (prefixWord ++ tailWord_7798003).sum := by decide
  have hdescent : baseEnd_7798003 < baseStart_7798003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798044 : List Nat := [2, 2, 3, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_7798044 : Nat := 118140960795 + 7798044 * 2 ^ 59
def prefixEnd_7798044 : Nat := 4983230072969 + 3 ^ 40 * 7798044 * 2
def baseEnd_7798044 : Nat := 4004144736909393350687455

theorem tailTrace_7798044 : CollatzResearch.WordTrace tailWord_7798044 prefixEnd_7798044 4004144736909393350687455 := by
  unfold tailWord_7798044
  simp only [CollatzResearch.WordTrace]
  refine ⟨142209015280512931365152593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189612020374017241820203457 142209015280512931365152593)
  ·
    refine ⟨106656761460384698523864445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142209015280512931365152593 106656761460384698523864445)
    ·
      refine ⟨39996285547644261946449167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106656761460384698523864445 39996285547644261946449167)
      ·
        refine ⟨59994428321466392919673751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39996285547644261946449167 59994428321466392919673751)
        ·
          refine ⟨89991642482199589379510627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59994428321466392919673751 89991642482199589379510627)
          ·
            refine ⟨134987463723299384069265941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89991642482199589379510627 134987463723299384069265941)
            ·
              refine ⟨6327537362029658628246841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134987463723299384069265941 6327537362029658628246841)
              ·
                refine ⟨4745653021522243971185131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6327537362029658628246841 4745653021522243971185131)
                ·
                  refine ⟨7118479532283365956777697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745653021522243971185131 7118479532283365956777697)
                  ·
                    refine ⟨5338859649212524467583273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7118479532283365956777697 5338859649212524467583273)
                    ·
                      refine ⟨4004144736909393350687455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338859649212524467583273 4004144736909393350687455)
                      ·
                        rfl

theorem cell23_7798044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_7798044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798044 prefixEnd_7798044 := by exact prefixLift 7798044
  have htrace : WordTrace (prefixWord ++ tailWord_7798044) baseStart_7798044 baseEnd_7798044 := by
    simpa [prefixWord, tailWord_7798044, baseEnd_7798044] using wordTrace_append hprefix tailTrace_7798044
  have hstable : (prefixWord ++ tailWord_7798044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798044).length < 2 ^ (prefixWord ++ tailWord_7798044).sum := by decide
  have hdescent : baseEnd_7798044 < baseStart_7798044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798050 : List Nat := [3, 3, 1, 1, 5, 1, 1, 8]
def baseStart_7798050 : Nat := 118140960795 + 7798050 * 2 ^ 59
def prefixEnd_7798050 : Nat := 4983230072969 + 3 ^ 40 * 7798050 * 2
def baseEnd_7798050 : Nat := 148301771029382234341201

theorem tailTrace_7798050 : CollatzResearch.WordTrace tailWord_7798050 prefixEnd_7798050 148301771029382234341201 := by
  unfold tailWord_7798050
  simp only [CollatzResearch.WordTrace]
  refine ⟨71104562349751031438755901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189612166266002750503349069 71104562349751031438755901)
  ·
    refine ⟨26664210881156636789533463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71104562349751031438755901 26664210881156636789533463)
    ·
      refine ⟨39996316321734955184300195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26664210881156636789533463 39996316321734955184300195)
      ·
        refine ⟨59994474482602432776450293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39996316321734955184300195 59994474482602432776450293)
        ·
          refine ⟨5624481982743978072792215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59994474482602432776450293 5624481982743978072792215)
          ·
            refine ⟨8436722974115967109188323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624481982743978072792215 8436722974115967109188323)
            ·
              refine ⟨12655084461173950663782485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436722974115967109188323 12655084461173950663782485)
              ·
                refine ⟨148301771029382234341201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12655084461173950663782485 148301771029382234341201)
                ·
                  rfl

theorem cell23_7798050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 8].length) (baseStart_7798050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798050 prefixEnd_7798050 := by exact prefixLift 7798050
  have htrace : WordTrace (prefixWord ++ tailWord_7798050) baseStart_7798050 baseEnd_7798050 := by
    simpa [prefixWord, tailWord_7798050, baseEnd_7798050] using wordTrace_append hprefix tailTrace_7798050
  have hstable : (prefixWord ++ tailWord_7798050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798050).length < 2 ^ (prefixWord ++ tailWord_7798050).sum := by decide
  have hdescent : baseEnd_7798050 < baseStart_7798050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798087 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_7798087 : Nat := 118140960795 + 7798087 * 2 ^ 59
def prefixEnd_7798087 : Nat := 4983230072969 + 3 ^ 40 * 7798087 * 2
def baseEnd_7798087 : Nat := 4004166816577536682449757

theorem tailTrace_7798087 : CollatzResearch.WordTrace tailWord_7798087 prefixEnd_7798087 4004166816577536682449757 := by
  unfold tailWord_7798087
  simp only [CollatzResearch.WordTrace]
  refine ⟨284419598899870081074120515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189613065933246720716080343 284419598899870081074120515)
  ·
    refine ⟨426629398349805121611180773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284419598899870081074120515 426629398349805121611180773)
    ·
      refine ⟨79993012190588460302096395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426629398349805121611180773 79993012190588460302096395)
      ·
        refine ⟨119989518285882690453144593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79993012190588460302096395 119989518285882690453144593)
        ·
          refine ⟨89992138714412017839858445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119989518285882690453144593 89992138714412017839858445)
          ·
            refine ⟨33747052017904506689946917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89992138714412017839858445 33747052017904506689946917)
            ·
              refine ⟨6327572253357095004365047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33747052017904506689946917 6327572253357095004365047)
              ·
                refine ⟨9491358380035642506547571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327572253357095004365047 9491358380035642506547571)
                ·
                  refine ⟨14237037570053463759821357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9491358380035642506547571 14237037570053463759821357)
                  ·
                    refine ⟨5338889088770048909933009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14237037570053463759821357 5338889088770048909933009)
                    ·
                      refine ⟨4004166816577536682449757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338889088770048909933009 4004166816577536682449757)
                      ·
                        rfl

theorem cell23_7798087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_7798087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798087 prefixEnd_7798087 := by exact prefixLift 7798087
  have htrace : WordTrace (prefixWord ++ tailWord_7798087) baseStart_7798087 baseEnd_7798087 := by
    simpa [prefixWord, tailWord_7798087, baseEnd_7798087] using wordTrace_append hprefix tailTrace_7798087
  have hstable : (prefixWord ++ tailWord_7798087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798087).length < 2 ^ (prefixWord ++ tailWord_7798087).sum := by decide
  have hdescent : baseEnd_7798087 < baseStart_7798087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798096 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_7798096 : Nat := 118140960795 + 7798096 * 2 ^ 59
def prefixEnd_7798096 : Nat := 4983230072969 + 3 ^ 40 * 7798096 * 2
def baseEnd_7798096 : Nat := 4004171437903427147237215

theorem tailTrace_7798096 : CollatzResearch.WordTrace tailWord_7798096 prefixEnd_7798096 4004171437903427147237215 := by
  unfold tailWord_7798096
  simp only [CollatzResearch.WordTrace]
  refine ⟨142209963578418737805599071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189613284771224983740798761 142209963578418737805599071)
  ·
    refine ⟨213314945367628106708398607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142209963578418737805599071 213314945367628106708398607)
    ·
      refine ⟨319972418051442160062597911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213314945367628106708398607 319972418051442160062597911)
      ·
        refine ⟨479958627077163240093896867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319972418051442160062597911 479958627077163240093896867)
        ·
          refine ⟨719937940615744860140845301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479958627077163240093896867 719937940615744860140845301)
          ·
            refine ⟨67494181932726080638204247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 719937940615744860140845301 67494181932726080638204247)
            ·
              refine ⟨101241272899089120957306371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67494181932726080638204247 101241272899089120957306371)
              ·
                refine ⟨151861909348633681435959557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101241272899089120957306371 151861909348633681435959557)
                ·
                  refine ⟨28474108002868815269242417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151861909348633681435959557 28474108002868815269242417)
                  ·
                    refine ⟨21355581002151611451931813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28474108002868815269242417 21355581002151611451931813)
                    ·
                      refine ⟨4004171437903427147237215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21355581002151611451931813 4004171437903427147237215)
                      ·
                        rfl

theorem cell23_7798096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_7798096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798096 prefixEnd_7798096 := by exact prefixLift 7798096
  have htrace : WordTrace (prefixWord ++ tailWord_7798096) baseStart_7798096 baseEnd_7798096 := by
    simpa [prefixWord, tailWord_7798096, baseEnd_7798096] using wordTrace_append hprefix tailTrace_7798096
  have hstable : (prefixWord ++ tailWord_7798096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798096).length < 2 ^ (prefixWord ++ tailWord_7798096).sum := by decide
  have hdescent : baseEnd_7798096 < baseStart_7798096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798106 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 7]
def baseStart_7798106 : Nat := 118140960795 + 7798106 * 2 ^ 59
def prefixEnd_7798106 : Nat := 4983230072969 + 3 ^ 40 * 7798106 * 2
def baseEnd_7798106 : Nat := 444908508078885789790241

theorem tailTrace_7798106 : CollatzResearch.WordTrace tailWord_7798106 prefixEnd_7798106 444908508078885789790241 := by
  unfold tailWord_7798106
  simp only [CollatzResearch.WordTrace]
  refine ⟨71105072971700311829765543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189613527924534164879374781 71105072971700311829765543)
  ·
    refine ⟨106657609457550467744648315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71105072971700311829765543 106657609457550467744648315)
    ·
      refine ⟨159986414186325701616972473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106657609457550467744648315 159986414186325701616972473)
      ·
        refine ⟨119989810639744276212729355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159986414186325701616972473 119989810639744276212729355)
        ·
          refine ⟨179984715959616414319094033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119989810639744276212729355 179984715959616414319094033)
          ·
            refine ⟨134988536969712310739320525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179984715959616414319094033 134988536969712310739320525)
            ·
              refine ⟨50620701363642116527245197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134988536969712310739320525 50620701363642116527245197)
              ·
                refine ⟨18982763011365793697716949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50620701363642116527245197 18982763011365793697716949)
                ·
                  refine ⟨444908508078885789790241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18982763011365793697716949 444908508078885789790241)
                  ·
                    rfl

theorem cell23_7798106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_7798106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798106 prefixEnd_7798106 := by exact prefixLift 7798106
  have htrace : WordTrace (prefixWord ++ tailWord_7798106) baseStart_7798106 baseEnd_7798106 := by
    simpa [prefixWord, tailWord_7798106, baseEnd_7798106] using wordTrace_append hprefix tailTrace_7798106
  have hstable : (prefixWord ++ tailWord_7798106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798106).length < 2 ^ (prefixWord ++ tailWord_7798106).sum := by decide
  have hdescent : baseEnd_7798106 < baseStart_7798106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798136 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 8, 5]
def baseStart_7798136 : Nat := 118140960795 + 7798136 * 2 ^ 59
def prefixEnd_7798136 : Nat := 4983230072969 + 3 ^ 40 * 7798136 * 2
def baseEnd_7798136 : Nat := 1334730659043202330245677

theorem tailTrace_7798136 : CollatzResearch.WordTrace tailWord_7798136 prefixEnd_7798136 1334730659043202330245677 := by
  unfold tailWord_7798136
  simp only [CollatzResearch.WordTrace]
  refine ⟨142210693038346281221327131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189614257384461708295102841 142210693038346281221327131)
  ·
    refine ⟨213316039557519421831990697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142210693038346281221327131 213316039557519421831990697)
    ·
      refine ⟨159987029668139566373993023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213316039557519421831990697 159987029668139566373993023)
      ·
        refine ⟨239980544502209349560989535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159987029668139566373993023 239980544502209349560989535)
        ·
          refine ⟨359970816753314024341484303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239980544502209349560989535 359970816753314024341484303)
          ·
            refine ⟨539956225129971036512226455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359970816753314024341484303 539956225129971036512226455)
            ·
              refine ⟨809934337694956554768339683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539956225129971036512226455 809934337694956554768339683)
              ·
                refine ⟨1214901506542434832152509525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809934337694956554768339683 1214901506542434832152509525)
                ·
                  refine ⟨14237127029794158189287221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1214901506542434832152509525 14237127029794158189287221)
                  ·
                    refine ⟨1334730659043202330245677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14237127029794158189287221 1334730659043202330245677)
                    ·
                      rfl

theorem cell23_7798136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_7798136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798136 prefixEnd_7798136 := by exact prefixLift 7798136
  have htrace : WordTrace (prefixWord ++ tailWord_7798136) baseStart_7798136 baseEnd_7798136 := by
    simpa [prefixWord, tailWord_7798136, baseEnd_7798136] using wordTrace_append hprefix tailTrace_7798136
  have hstable : (prefixWord ++ tailWord_7798136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798136).length < 2 ^ (prefixWord ++ tailWord_7798136).sum := by decide
  have hdescent : baseEnd_7798136 < baseStart_7798136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798168 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7798168 : Nat := 118140960795 + 7798168 * 2 ^ 59
def prefixEnd_7798168 : Nat := 4983230072969 + 3 ^ 40 * 7798168 * 2
def baseEnd_7798168 : Nat := 4004208408510550865536885

theorem tailTrace_7798168 : CollatzResearch.WordTrace tailWord_7798168 prefixEnd_7798168 4004208408510550865536885 := by
  unfold tailWord_7798168
  simp only [CollatzResearch.WordTrace]
  refine ⟨142211276606288315953909579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189615035475051087938546105 142211276606288315953909579)
  ·
    refine ⟨213316914909432473930864369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142211276606288315953909579 213316914909432473930864369)
    ·
      refine ⟨159987686182074355448148277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213316914909432473930864369 159987686182074355448148277)
      ·
        refine ⟨14998845579569470823263901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159987686182074355448148277 14998845579569470823263901)
        ·
          refine ⟨5624567092338551558723963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14998845579569470823263901 5624567092338551558723963)
          ·
            refine ⟨8436850638507827338085945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624567092338551558723963 8436850638507827338085945)
            ·
              refine ⟨6327637978880870503564459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8436850638507827338085945 6327637978880870503564459)
              ·
                refine ⟨9491456968321305755346689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327637978880870503564459 9491456968321305755346689)
                ·
                  refine ⟨7118592726240979316510017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491456968321305755346689 7118592726240979316510017)
                  ·
                    refine ⟨5338944544680734487382513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7118592726240979316510017 5338944544680734487382513)
                    ·
                      refine ⟨4004208408510550865536885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5338944544680734487382513 4004208408510550865536885)
                      ·
                        rfl

theorem cell23_7798168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7798168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798168 prefixEnd_7798168 := by exact prefixLift 7798168
  have htrace : WordTrace (prefixWord ++ tailWord_7798168) baseStart_7798168 baseEnd_7798168 := by
    simpa [prefixWord, tailWord_7798168, baseEnd_7798168] using wordTrace_append hprefix tailTrace_7798168
  have hstable : (prefixWord ++ tailWord_7798168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798168).length < 2 ^ (prefixWord ++ tailWord_7798168).sum := by decide
  have hdescent : baseEnd_7798168 < baseStart_7798168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798263 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_7798263 : Nat := 118140960795 + 7798263 * 2 ^ 59
def prefixEnd_7798263 : Nat := 4983230072969 + 3 ^ 40 * 7798263 * 2
def baseEnd_7798263 : Nat := 4004257189172727993848947

theorem tailTrace_7798263 : CollatzResearch.WordTrace tailWord_7798263 prefixEnd_7798263 4004257189172727993848947 := by
  unfold tailWord_7798263
  simp only [CollatzResearch.WordTrace]
  refine ⟨284426018147232463132527443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189617345431488308755018295 284426018147232463132527443)
  ·
    refine ⟨426639027220848694698791165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284426018147232463132527443 426639027220848694698791165)
    ·
      refine ⟨159989635207818260512046687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426639027220848694698791165 159989635207818260512046687)
      ·
        refine ⟨239984452811727390768070031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159989635207818260512046687 239984452811727390768070031)
        ·
          refine ⟨359976679217591086152105047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239984452811727390768070031 359976679217591086152105047)
          ·
            refine ⟨539965018826386629228157571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359976679217591086152105047 539965018826386629228157571)
            ·
              refine ⟨809947528239579943842236357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539965018826386629228157571 809947528239579943842236357)
              ·
                refine ⟨151865161544921239470419317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 809947528239579943842236357 151865161544921239470419317)
                ·
                  refine ⟨14237358894836366200351811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151865161544921239470419317 14237358894836366200351811)
                  ·
                    refine ⟨21356038342254549300527717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14237358894836366200351811 21356038342254549300527717)
                    ·
                      refine ⟨4004257189172727993848947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21356038342254549300527717 4004257189172727993848947)
                      ·
                        rfl

theorem cell23_7798263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_7798263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798263 prefixEnd_7798263 := by exact prefixLift 7798263
  have htrace : WordTrace (prefixWord ++ tailWord_7798263) baseStart_7798263 baseEnd_7798263 := by
    simpa [prefixWord, tailWord_7798263, baseEnd_7798263] using wordTrace_append hprefix tailTrace_7798263
  have hstable : (prefixWord ++ tailWord_7798263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798263).length < 2 ^ (prefixWord ++ tailWord_7798263).sum := by decide
  have hdescent : baseEnd_7798263 < baseStart_7798263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798274 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_7798274 : Nat := 118140960795 + 7798274 * 2 ^ 59
def prefixEnd_7798274 : Nat := 4983230072969 + 3 ^ 40 * 7798274 * 2
def baseEnd_7798274 : Nat := 4004262837459927450811397

theorem tailTrace_7798274 : CollatzResearch.WordTrace tailWord_7798274 prefixEnd_7798274 4004262837459927450811397 := by
  unfold tailWord_7798274
  simp only [CollatzResearch.WordTrace]
  refine ⟨71106604837548153002794469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189617612900128408007451917 71106604837548153002794469)
  ·
    refine ⟨13332488407040278688023963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71106604837548153002794469 13332488407040278688023963)
    ·
      refine ⟨19998732610560418032035945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13332488407040278688023963 19998732610560418032035945)
      ·
        refine ⟨14999049457920313524026959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19998732610560418032035945 14999049457920313524026959)
        ·
          refine ⟨22498574186880470286040439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14999049457920313524026959 22498574186880470286040439)
          ·
            refine ⟨33747861280320705429060659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22498574186880470286040439 33747861280320705429060659)
            ·
              refine ⟨50621791920481058143590989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33747861280320705429060659 50621791920481058143590989)
              ·
                refine ⟨18983171970180396803846621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50621791920481058143590989 18983171970180396803846621)
                ·
                  refine ⟨7118689488817648801442483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18983171970180396803846621 7118689488817648801442483)
                  ·
                    refine ⟨10678034233226473202163725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7118689488817648801442483 10678034233226473202163725)
                    ·
                      refine ⟨4004262837459927450811397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10678034233226473202163725 4004262837459927450811397)
                      ·
                        rfl

theorem cell23_7798274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_7798274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798274 prefixEnd_7798274 := by exact prefixLift 7798274
  have htrace : WordTrace (prefixWord ++ tailWord_7798274) baseStart_7798274 baseEnd_7798274 := by
    simpa [prefixWord, tailWord_7798274, baseEnd_7798274] using wordTrace_append hprefix tailTrace_7798274
  have hstable : (prefixWord ++ tailWord_7798274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798274).length < 2 ^ (prefixWord ++ tailWord_7798274).sum := by decide
  have hdescent : baseEnd_7798274 < baseStart_7798274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798302 : List Nat := [4, 3, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7798302 : Nat := 118140960795 + 7798302 * 2 ^ 59
def prefixEnd_7798302 : Nat := 4983230072969 + 3 ^ 40 * 7798302 * 2
def baseEnd_7798302 : Nat := 1334759071639417780420423

theorem tailTrace_7798302 : CollatzResearch.WordTrace tailWord_7798302 prefixEnd_7798302 1334759071639417780420423 := by
  unfold tailWord_7798302
  simp only [CollatzResearch.WordTrace]
  refine ⟨35553430074261396599149645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189618293729394115195464773 35553430074261396599149645)
  ·
    refine ⟨13332536277848023724681117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35553430074261396599149645 13332536277848023724681117)
    ·
      refine ⟨4999701104193008896755419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13332536277848023724681117 4999701104193008896755419)
      ·
        refine ⟨7499551656289513345133129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999701104193008896755419 7499551656289513345133129)
        ·
          refine ⟨5624663742217135008849847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7499551656289513345133129 5624663742217135008849847)
          ·
            refine ⟨8436995613325702513274771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624663742217135008849847 8436995613325702513274771)
            ·
              refine ⟨12655493419988553769912157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436995613325702513274771 12655493419988553769912157)
              ·
                refine ⟨4745810032495707663717059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12655493419988553769912157 4745810032495707663717059)
                ·
                  refine ⟨7118715048743561495575589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745810032495707663717059 7118715048743561495575589)
                  ·
                    refine ⟨1334759071639417780420423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7118715048743561495575589 1334759071639417780420423)
                    ·
                      rfl

theorem cell23_7798302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7798302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798302 prefixEnd_7798302 := by exact prefixLift 7798302
  have htrace : WordTrace (prefixWord ++ tailWord_7798302) baseStart_7798302 baseEnd_7798302 := by
    simpa [prefixWord, tailWord_7798302, baseEnd_7798302] using wordTrace_append hprefix tailTrace_7798302
  have hstable : (prefixWord ++ tailWord_7798302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798302).length < 2 ^ (prefixWord ++ tailWord_7798302).sum := by decide
  have hdescent : baseEnd_7798302 < baseStart_7798302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798381 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_7798381 : Nat := 118140960795 + 7798381 * 2 ^ 59
def prefixEnd_7798381 : Nat := 4983230072969 + 3 ^ 40 * 7798381 * 2
def baseEnd_7798381 : Nat := 4004317779889958532173405

theorem tailTrace_7798381 : CollatzResearch.WordTrace tailWord_7798381 prefixEnd_7798381 4004317779889958532173405 := by
  unfold tailWord_7798381
  simp only [CollatzResearch.WordTrace]
  refine ⟨284430321960804969285322997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189620214640536646190215331 284430321960804969285322997)
  ·
    refine ⟨26665342683825465870499031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284430321960804969285322997 26665342683825465870499031)
    ·
      refine ⟨39998014025738198805748547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26665342683825465870499031 39998014025738198805748547)
      ·
        refine ⟨59997021038607298208622821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39998014025738198805748547 59997021038607298208622821)
        ·
          refine ⟨11249441444738868414116779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59997021038607298208622821 11249441444738868414116779)
          ·
            refine ⟨16874162167108302621175169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11249441444738868414116779 16874162167108302621175169)
            ·
              refine ⟨12655621625331226965881377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16874162167108302621175169 12655621625331226965881377)
              ·
                refine ⟨9491716218998420224411033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12655621625331226965881377 9491716218998420224411033)
                ·
                  refine ⟨7118787164248815168308275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491716218998420224411033 7118787164248815168308275)
                  ·
                    refine ⟨10678180746373222752462413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7118787164248815168308275 10678180746373222752462413)
                    ·
                      refine ⟨4004317779889958532173405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10678180746373222752462413 4004317779889958532173405)
                      ·
                        rfl

theorem cell23_7798381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_7798381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798381 prefixEnd_7798381 := by exact prefixLift 7798381
  have htrace : WordTrace (prefixWord ++ tailWord_7798381) baseStart_7798381 baseEnd_7798381 := by
    simpa [prefixWord, tailWord_7798381, baseEnd_7798381] using wordTrace_append hprefix tailTrace_7798381
  have hstable : (prefixWord ++ tailWord_7798381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798381).length < 2 ^ (prefixWord ++ tailWord_7798381).sum := by decide
  have hdescent : baseEnd_7798381 < baseStart_7798381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798382 : List Nat := [4, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_7798382 : Nat := 118140960795 + 7798382 * 2 ^ 59
def prefixEnd_7798382 : Nat := 4983230072969 + 3 ^ 40 * 7798382 * 2
def baseEnd_7798382 : Nat := 4004318293370613028260901

theorem tailTrace_7798382 : CollatzResearch.WordTrace tailWord_7798382 prefixEnd_7798382 4004318293370613028260901 := by
  unfold tailWord_7798382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35553794804225168307013675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189620238955867564304072933 35553794804225168307013675)
  ·
    refine ⟨53330692206337752460520513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35553794804225168307013675 53330692206337752460520513)
    ·
      refine ⟨39998019154753314345390385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53330692206337752460520513 39998019154753314345390385)
      ·
        refine ⟨29998514366064985759042789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39998019154753314345390385 29998514366064985759042789)
        ·
          refine ⟨5624721443637184829820523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29998514366064985759042789 5624721443637184829820523)
          ·
            refine ⟨8437082165455777244730785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624721443637184829820523 8437082165455777244730785)
            ·
              refine ⟨6327811624091832933548089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8437082165455777244730785 6327811624091832933548089)
              ·
                refine ⟨4745858718068874700161067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6327811624091832933548089 4745858718068874700161067)
                ·
                  refine ⟨7118788077103312050241601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745858718068874700161067 7118788077103312050241601)
                  ·
                    refine ⟨5339091057827484037681201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7118788077103312050241601 5339091057827484037681201)
                    ·
                      refine ⟨4004318293370613028260901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339091057827484037681201 4004318293370613028260901)
                      ·
                        rfl

theorem cell23_7798382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_7798382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798382 prefixEnd_7798382 := by exact prefixLift 7798382
  have htrace : WordTrace (prefixWord ++ tailWord_7798382) baseStart_7798382 baseEnd_7798382 := by
    simpa [prefixWord, tailWord_7798382, baseEnd_7798382] using wordTrace_append hprefix tailTrace_7798382
  have hstable : (prefixWord ++ tailWord_7798382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798382).length < 2 ^ (prefixWord ++ tailWord_7798382).sum := by decide
  have hdescent : baseEnd_7798382 < baseStart_7798382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798383 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_7798383 : Nat := 118140960795 + 7798383 * 2 ^ 59
def prefixEnd_7798383 : Nat := 4983230072969 + 3 ^ 40 * 7798383 * 2
def baseEnd_7798383 : Nat := 4004318806851267524348395

theorem tailTrace_7798383 : CollatzResearch.WordTrace tailWord_7798383 prefixEnd_7798383 4004318806851267524348395 := by
  unfold tailWord_7798383
  simp only [CollatzResearch.WordTrace]
  refine ⟨284430394906797723626895803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189620263271198482417930535 284430394906797723626895803)
  ·
    refine ⟨426645592360196585440343705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284430394906797723626895803 426645592360196585440343705)
    ·
      refine ⟨319984194270147439080257779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426645592360196585440343705 319984194270147439080257779)
      ·
        refine ⟨479976291405221158620386669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319984194270147439080257779 479976291405221158620386669)
        ·
          refine ⟨179991109276957934482645001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479976291405221158620386669 179991109276957934482645001)
          ·
            refine ⟨134993331957718450861983751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179991109276957934482645001 134993331957718450861983751)
            ·
              refine ⟨202489997936577676292975627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134993331957718450861983751 202489997936577676292975627)
              ·
                refine ⟨303734996904866514439463441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202489997936577676292975627 303734996904866514439463441)
                ·
                  refine ⟨227801247678649885829597581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303734996904866514439463441 227801247678649885829597581)
                  ·
                    refine ⟨85425467879493707186099093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227801247678649885829597581 85425467879493707186099093)
                    ·
                      refine ⟨4004318806851267524348395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85425467879493707186099093 4004318806851267524348395)
                      ·
                        rfl

theorem cell23_7798383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_7798383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798383 prefixEnd_7798383 := by exact prefixLift 7798383
  have htrace : WordTrace (prefixWord ++ tailWord_7798383) baseStart_7798383 baseEnd_7798383 := by
    simpa [prefixWord, tailWord_7798383, baseEnd_7798383] using wordTrace_append hprefix tailTrace_7798383
  have hstable : (prefixWord ++ tailWord_7798383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798383).length < 2 ^ (prefixWord ++ tailWord_7798383).sum := by decide
  have hdescent : baseEnd_7798383 < baseStart_7798383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798387 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 8, 2, 2]
def baseStart_7798387 : Nat := 118140960795 + 7798387 * 2 ^ 59
def prefixEnd_7798387 : Nat := 4983230072969 + 3 ^ 40 * 7798387 * 2
def baseEnd_7798387 : Nat := 4004320860773885508698377

theorem tailTrace_7798387 : CollatzResearch.WordTrace tailWord_7798387 prefixEnd_7798387 4004320860773885508698377 := by
  unfold tailWord_7798387
  simp only [CollatzResearch.WordTrace]
  refine ⟨284430540798783232310041415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189620360532522154873360943 284430540798783232310041415)
  ·
    refine ⟨426645811198174848465062123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284430540798783232310041415 426645811198174848465062123)
    ·
      refine ⟨639968716797262272697593185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426645811198174848465062123 639968716797262272697593185)
      ·
        refine ⟨479976537597946704523194889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639968716797262272697593185 479976537597946704523194889)
        ·
          refine ⟨359982403198460028392396167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479976537597946704523194889 359982403198460028392396167)
          ·
            refine ⟨539973604797690042588594251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359982403198460028392396167 539973604797690042588594251)
            ·
              refine ⟨809960407196535063882891377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539973604797690042588594251 809960407196535063882891377)
              ·
                refine ⟨607470305397401297912168533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809960407196535063882891377 607470305397401297912168533)
                ·
                  refine ⟨7118792641375796459908225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 607470305397401297912168533 7118792641375796459908225)
                  ·
                    refine ⟨5339094481031847344931169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7118792641375796459908225 5339094481031847344931169)
                    ·
                      refine ⟨4004320860773885508698377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339094481031847344931169 4004320860773885508698377)
                      ·
                        rfl

theorem cell23_7798387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 2, 2].length) (baseStart_7798387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798387 prefixEnd_7798387 := by exact prefixLift 7798387
  have htrace : WordTrace (prefixWord ++ tailWord_7798387) baseStart_7798387 baseEnd_7798387 := by
    simpa [prefixWord, tailWord_7798387, baseEnd_7798387] using wordTrace_append hprefix tailTrace_7798387
  have hstable : (prefixWord ++ tailWord_7798387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798387).length < 2 ^ (prefixWord ++ tailWord_7798387).sum := by decide
  have hdescent : baseEnd_7798387 < baseStart_7798387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798400 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_7798400 : Nat := 118140960795 + 7798400 * 2 ^ 59
def prefixEnd_7798400 : Nat := 4983230072969 + 3 ^ 40 * 7798400 * 2
def baseEnd_7798400 : Nat := 4004327536022393957835817

theorem tailTrace_7798400 : CollatzResearch.WordTrace tailWord_7798400 prefixEnd_7798400 4004327536022393957835817 := by
  unfold tailWord_7798400
  simp only [CollatzResearch.WordTrace]
  refine ⟨142215507473868067765132327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189620676631824090353509769 142215507473868067765132327)
  ·
    refine ⟨213323261210802101647698491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142215507473868067765132327 213323261210802101647698491)
    ·
      refine ⟨319984891816203152471547737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213323261210802101647698491 319984891816203152471547737)
      ·
        refine ⟨239988668862152364353660803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319984891816203152471547737 239988668862152364353660803)
        ·
          refine ⟨359983003293228546530491205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239988668862152364353660803 359983003293228546530491205)
          ·
            refine ⟨67496813117480352474467101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359983003293228546530491205 67496813117480352474467101)
            ·
              refine ⟨25311304919055132177925163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67496813117480352474467101 25311304919055132177925163)
              ·
                refine ⟨37966957378582698266887745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25311304919055132177925163 37966957378582698266887745)
                ·
                  refine ⟨28475218033937023700165809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37966957378582698266887745 28475218033937023700165809)
                  ·
                    refine ⟨21356413525452767775124357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28475218033937023700165809 21356413525452767775124357)
                    ·
                      refine ⟨4004327536022393957835817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21356413525452767775124357 4004327536022393957835817)
                      ·
                        rfl

theorem cell23_7798400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_7798400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798400 prefixEnd_7798400 := by exact prefixLift 7798400
  have htrace : WordTrace (prefixWord ++ tailWord_7798400) baseStart_7798400 baseEnd_7798400 := by
    simpa [prefixWord, tailWord_7798400, baseEnd_7798400] using wordTrace_append hprefix tailTrace_7798400
  have hstable : (prefixWord ++ tailWord_7798400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798400).length < 2 ^ (prefixWord ++ tailWord_7798400).sum := by decide
  have hdescent : baseEnd_7798400 < baseStart_7798400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798410 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 9]
def baseStart_7798410 : Nat := 118140960795 + 7798410 * 2 ^ 59
def prefixEnd_7798410 : Nat := 4983230072969 + 3 ^ 40 * 7798410 * 2
def baseEnd_7798410 : Nat := 444925852314326546523419

theorem tailTrace_7798410 : CollatzResearch.WordTrace tailWord_7798410 prefixEnd_7798410 444925852314326546523419 := by
  unfold tailWord_7798410
  simp only [CollatzResearch.WordTrace]
  refine ⟨71107844919424976809532171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189620919785133271492085789 71107844919424976809532171)
  ·
    refine ⟨106661767379137465214298257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71107844919424976809532171 106661767379137465214298257)
    ·
      refine ⟨79996325534353098910723693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106661767379137465214298257 79996325534353098910723693)
      ·
        refine ⟨29998622075382412091521385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79996325534353098910723693 29998622075382412091521385)
        ·
          refine ⟨22498966556536809068641039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29998622075382412091521385 22498966556536809068641039)
          ·
            refine ⟨33748449834805213602961559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22498966556536809068641039 33748449834805213602961559)
            ·
              refine ⟨50622674752207820404442339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33748449834805213602961559 50622674752207820404442339)
              ·
                refine ⟨75934012128311730606663509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50622674752207820404442339 75934012128311730606663509)
                ·
                  refine ⟨444925852314326546523419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75934012128311730606663509 444925852314326546523419)
                  ·
                    rfl

theorem cell23_7798410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_7798410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798410 prefixEnd_7798410 := by exact prefixLift 7798410
  have htrace : WordTrace (prefixWord ++ tailWord_7798410) baseStart_7798410 baseEnd_7798410 := by
    simpa [prefixWord, tailWord_7798410, baseEnd_7798410] using wordTrace_append hprefix tailTrace_7798410
  have hstable : (prefixWord ++ tailWord_7798410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798410).length < 2 ^ (prefixWord ++ tailWord_7798410).sum := by decide
  have hdescent : baseEnd_7798410 < baseStart_7798410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798450 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_7798450 : Nat := 118140960795 + 7798450 * 2 ^ 59
def prefixEnd_7798450 : Nat := 4983230072969 + 3 ^ 40 * 7798450 * 2
def baseEnd_7798450 : Nat := 4004353210055118762210587

theorem tailTrace_7798450 : CollatzResearch.WordTrace tailWord_7798450 prefixEnd_7798450 4004353210055118762210587 := by
  unfold tailWord_7798450
  simp only [CollatzResearch.WordTrace]
  refine ⟨71108209649388748517396201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189621892398369996046389869 71108209649388748517396201)
  ·
    refine ⟨53331157237041561388047151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71108209649388748517396201 53331157237041561388047151)
    ·
      refine ⟨79996735855562342082070727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53331157237041561388047151 79996735855562342082070727)
      ·
        refine ⟨119995103783343513123106091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79996735855562342082070727 119995103783343513123106091)
        ·
          refine ⟨179992655675015269684659137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119995103783343513123106091 179992655675015269684659137)
          ·
            refine ⟨134994491756261452263494353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179992655675015269684659137 134994491756261452263494353)
            ·
              refine ⟨101245868817196089197620765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134994491756261452263494353 101245868817196089197620765)
              ·
                refine ⟨37967200806448533449107787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101245868817196089197620765 37967200806448533449107787)
                ·
                  refine ⟨56950801209672800173661681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37967200806448533449107787 56950801209672800173661681)
                  ·
                    refine ⟨42713100907254600130246261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56950801209672800173661681 42713100907254600130246261)
                    ·
                      refine ⟨4004353210055118762210587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42713100907254600130246261 4004353210055118762210587)
                      ·
                        rfl

theorem cell23_7798450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_7798450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798450 prefixEnd_7798450 := by exact prefixLift 7798450
  have htrace : WordTrace (prefixWord ++ tailWord_7798450) baseStart_7798450 baseEnd_7798450 := by
    simpa [prefixWord, tailWord_7798450, baseEnd_7798450] using wordTrace_append hprefix tailTrace_7798450
  have hstable : (prefixWord ++ tailWord_7798450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798450).length < 2 ^ (prefixWord ++ tailWord_7798450).sum := by decide
  have hdescent : baseEnd_7798450 < baseStart_7798450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798500 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 8]
def baseStart_7798500 : Nat := 118140960795 + 7798500 * 2 ^ 59
def prefixEnd_7798500 : Nat := 4983230072969 + 3 ^ 40 * 7798500 * 2
def baseEnd_7798500 : Nat := 444930987120871507398373

theorem tailTrace_7798500 : CollatzResearch.WordTrace tailWord_7798500 prefixEnd_7798500 444930987120871507398373 := by
  unfold tailWord_7798500
  simp only [CollatzResearch.WordTrace]
  refine ⟨142217331123686926304452477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189623108164915901739269969 142217331123686926304452477)
  ·
    refine ⟨53331499171382597364169679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142217331123686926304452477 53331499171382597364169679)
    ·
      refine ⟨79997248757073896046254519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53331499171382597364169679 79997248757073896046254519)
      ·
        refine ⟨119995873135610844069381779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79997248757073896046254519 119995873135610844069381779)
        ·
          refine ⟨179993809703416266104072669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119995873135610844069381779 179993809703416266104072669)
          ·
            refine ⟨67497678638781099789027251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179993809703416266104072669 67497678638781099789027251)
            ·
              refine ⟨101246517958171649683540877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67497678638781099789027251 101246517958171649683540877)
              ·
                refine ⟨37967444234314368631327829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101246517958171649683540877 37967444234314368631327829)
                ·
                  refine ⟨444930987120871507398373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37967444234314368631327829 444930987120871507398373)
                  ·
                    rfl

theorem cell23_7798500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_7798500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798500 prefixEnd_7798500 := by exact prefixLift 7798500
  have htrace : WordTrace (prefixWord ++ tailWord_7798500) baseStart_7798500 baseEnd_7798500 := by
    simpa [prefixWord, tailWord_7798500, baseEnd_7798500] using wordTrace_append hprefix tailTrace_7798500
  have hstable : (prefixWord ++ tailWord_7798500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798500).length < 2 ^ (prefixWord ++ tailWord_7798500).sum := by decide
  have hdescent : baseEnd_7798500 < baseStart_7798500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798504 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 3, 4]
def baseStart_7798504 : Nat := 118140960795 + 7798504 * 2 ^ 59
def prefixEnd_7798504 : Nat := 4983230072969 + 3 ^ 40 * 7798504 * 2
def baseEnd_7798504 : Nat := 1334793646003487183645113

theorem tailTrace_7798504 : CollatzResearch.WordTrace tailWord_7798504 prefixEnd_7798504 1334793646003487183645113 := by
  unfold tailWord_7798504
  simp only [CollatzResearch.WordTrace]
  refine ⟨142217404069679680646025283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189623205426239574194700377 142217404069679680646025283)
  ·
    refine ⟨213326106104519520969037925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142217404069679680646025283 213326106104519520969037925)
    ·
      refine ⟨39998644894597410181694611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213326106104519520969037925 39998644894597410181694611)
      ·
        refine ⟨59997967341896115272541917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39998644894597410181694611 59997967341896115272541917)
        ·
          refine ⟨22499237753211043227203219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59997967341896115272541917 22499237753211043227203219)
          ·
            refine ⟨33748856629816564840804829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22499237753211043227203219 33748856629816564840804829)
            ·
              refine ⟨12655821236181211815301811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33748856629816564840804829 12655821236181211815301811)
              ·
                refine ⟨18983731854271817722952717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12655821236181211815301811 18983731854271817722952717)
                ·
                  refine ⟨7118899445351931646107269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18983731854271817722952717 7118899445351931646107269)
                  ·
                    refine ⟨1334793646003487183645113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7118899445351931646107269 1334793646003487183645113)
                    ·
                      rfl

theorem cell23_7798504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_7798504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798504 prefixEnd_7798504 := by exact prefixLift 7798504
  have htrace : WordTrace (prefixWord ++ tailWord_7798504) baseStart_7798504 baseEnd_7798504 := by
    simpa [prefixWord, tailWord_7798504, baseEnd_7798504] using wordTrace_append hprefix tailTrace_7798504
  have hstable : (prefixWord ++ tailWord_7798504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798504).length < 2 ^ (prefixWord ++ tailWord_7798504).sum := by decide
  have hdescent : baseEnd_7798504 < baseStart_7798504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798577 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 1, 6]
def baseStart_7798577 : Nat := 118140960795 + 7798577 * 2 ^ 59
def prefixEnd_7798577 : Nat := 4983230072969 + 3 ^ 40 * 7798577 * 2
def baseEnd_7798577 : Nat := 1334806140699413255107501

theorem tailTrace_7798577 : CollatzResearch.WordTrace tailWord_7798577 prefixEnd_7798577 1334806140699413255107501 := by
  unfold tailWord_7798577
  simp only [CollatzResearch.WordTrace]
  refine ⟨284437470668094894759457985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189624980445396596506305323 284437470668094894759457985)
  ·
    refine ⟨213328103001071171069593489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284437470668094894759457985 213328103001071171069593489)
    ·
      refine ⟨159996077250803378302195117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213328103001071171069593489 159996077250803378302195117)
      ·
        refine ⟨59998528969051266863323169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159996077250803378302195117 59998528969051266863323169)
        ·
          refine ⟨44998896726788450147492377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59998528969051266863323169 44998896726788450147492377)
          ·
            refine ⟨33749172545091337610619283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44998896726788450147492377 33749172545091337610619283)
            ·
              refine ⟨50623758817637006415928925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33749172545091337610619283 50623758817637006415928925)
              ·
                refine ⟨18983909556613877405973347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50623758817637006415928925 18983909556613877405973347)
                ·
                  refine ⟨28475864334920816108960021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18983909556613877405973347 28475864334920816108960021)
                  ·
                    refine ⟨1334806140699413255107501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28475864334920816108960021 1334806140699413255107501)
                    ·
                      rfl

theorem cell23_7798577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_7798577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798577 prefixEnd_7798577 := by exact prefixLift 7798577
  have htrace : WordTrace (prefixWord ++ tailWord_7798577) baseStart_7798577 baseEnd_7798577 := by
    simpa [prefixWord, tailWord_7798577, baseEnd_7798577] using wordTrace_append hprefix tailTrace_7798577
  have hstable : (prefixWord ++ tailWord_7798577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798577).length < 2 ^ (prefixWord ++ tailWord_7798577).sum := by decide
  have hdescent : baseEnd_7798577 < baseStart_7798577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798597 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_7798597 : Nat := 118140960795 + 7798597 * 2 ^ 59
def prefixEnd_7798597 : Nat := 4983230072969 + 3 ^ 40 * 7798597 * 2
def baseEnd_7798597 : Nat := 4004428691711329687072411

theorem tailTrace_7798597 : CollatzResearch.WordTrace tailWord_7798597 prefixEnd_7798597 4004428691711329687072411 := by
  unfold tailWord_7798597
  simp only [CollatzResearch.WordTrace]
  refine ⟨284438200128022438175186045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189625466752014958783457363 284438200128022438175186045)
  ·
    refine ⟨106664325048008414315694767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284438200128022438175186045 106664325048008414315694767)
    ·
      refine ⟨159996487572012621473542151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106664325048008414315694767 159996487572012621473542151)
      ·
        refine ⟨239994731358018932210313227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159996487572012621473542151 239994731358018932210313227)
        ·
          refine ⟨359992097037028398315469841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239994731358018932210313227 359992097037028398315469841)
          ·
            refine ⟨269994072777771298736602381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359992097037028398315469841 269994072777771298736602381)
            ·
              refine ⟨101247777291664237026225893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269994072777771298736602381 101247777291664237026225893)
              ·
                refine ⟨18983958242187044442417355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101247777291664237026225893 18983958242187044442417355)
                ·
                  refine ⟨28475937363280566663626033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18983958242187044442417355 28475937363280566663626033)
                  ·
                    refine ⟨21356953022460424997719525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28475937363280566663626033 21356953022460424997719525)
                    ·
                      refine ⟨4004428691711329687072411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21356953022460424997719525 4004428691711329687072411)
                      ·
                        rfl

theorem cell23_7798597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_7798597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798597 prefixEnd_7798597 := by exact prefixLift 7798597
  have htrace : WordTrace (prefixWord ++ tailWord_7798597) baseStart_7798597 baseEnd_7798597 := by
    simpa [prefixWord, tailWord_7798597, baseEnd_7798597] using wordTrace_append hprefix tailTrace_7798597
  have hstable : (prefixWord ++ tailWord_7798597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798597).length < 2 ^ (prefixWord ++ tailWord_7798597).sum := by decide
  have hdescent : baseEnd_7798597 < baseStart_7798597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798598 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_7798598 : Nat := 118140960795 + 7798598 * 2 ^ 59
def prefixEnd_7798598 : Nat := 4983230072969 + 3 ^ 40 * 7798598 * 2
def baseEnd_7798598 : Nat := 1334809735063994727719969

theorem tailTrace_7798598 : CollatzResearch.WordTrace tailWord_7798598 prefixEnd_7798598 1334809735063994727719969 := by
  unfold tailWord_7798598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8888694893781837979561639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189625491067345876897314965 8888694893781837979561639)
  ·
    refine ⟨13333042340672756969342459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8888694893781837979561639 13333042340672756969342459)
    ·
      refine ⟨19999563511009135454013689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333042340672756969342459 19999563511009135454013689)
      ·
        refine ⟨14999672633256851590510267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19999563511009135454013689 14999672633256851590510267)
        ·
          refine ⟨22499508949885277385765401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14999672633256851590510267 22499508949885277385765401)
          ·
            refine ⟨16874631712413958039324051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22499508949885277385765401 16874631712413958039324051)
            ·
              refine ⟨25311947568620937058986077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16874631712413958039324051 25311947568620937058986077)
              ·
                refine ⟨9491980338232851397119779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25311947568620937058986077 9491980338232851397119779)
                ·
                  refine ⟨14237970507349277095679669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9491980338232851397119779 14237970507349277095679669)
                  ·
                    refine ⟨1334809735063994727719969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14237970507349277095679669 1334809735063994727719969)
                    ·
                      rfl

theorem cell23_7798598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_7798598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798598 prefixEnd_7798598 := by exact prefixLift 7798598
  have htrace : WordTrace (prefixWord ++ tailWord_7798598) baseStart_7798598 baseEnd_7798598 := by
    simpa [prefixWord, tailWord_7798598, baseEnd_7798598] using wordTrace_append hprefix tailTrace_7798598
  have hstable : (prefixWord ++ tailWord_7798598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798598).length < 2 ^ (prefixWord ++ tailWord_7798598).sum := by decide
  have hdescent : baseEnd_7798598 < baseStart_7798598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798618 : List Nat := [3, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2]
def baseStart_7798618 : Nat := 118140960795 + 7798618 * 2 ^ 59
def prefixEnd_7798618 : Nat := 4983230072969 + 3 ^ 40 * 7798618 * 2
def baseEnd_7798618 : Nat := 4004439474805074104909815

theorem tailTrace_7798618 : CollatzResearch.WordTrace tailWord_7798618 prefixEnd_7798618 4004439474805074104909815 := by
  unfold tailWord_7798618
  simp only [CollatzResearch.WordTrace]
  refine ⟨71109741515236589690425127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189625977373964239174467005 71109741515236589690425127)
  ·
    refine ⟨106664612272854884535637691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71109741515236589690425127 106664612272854884535637691)
    ·
      refine ⟨159996918409282326803456537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106664612272854884535637691 159996918409282326803456537)
      ·
        refine ⟨119997688806961745102592403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159996918409282326803456537 119997688806961745102592403)
        ·
          refine ⟨179996533210442617653888605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119997688806961745102592403 179996533210442617653888605)
          ·
            refine ⟨67498699953915981620208227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179996533210442617653888605 67498699953915981620208227)
            ·
              refine ⟨101248049930873972430312341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67498699953915981620208227 101248049930873972430312341)
              ·
                refine ⟨4746002340509717457670891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101248049930873972430312341 4746002340509717457670891)
                ·
                  refine ⟨7119003510764576186506337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746002340509717457670891 7119003510764576186506337)
                  ·
                    refine ⟨5339252633073432139879753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7119003510764576186506337 5339252633073432139879753)
                    ·
                      refine ⟨4004439474805074104909815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339252633073432139879753 4004439474805074104909815)
                      ·
                        rfl

theorem cell23_7798618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_7798618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798618 prefixEnd_7798618 := by exact prefixLift 7798618
  have htrace : WordTrace (prefixWord ++ tailWord_7798618) baseStart_7798618 baseEnd_7798618 := by
    simpa [prefixWord, tailWord_7798618, baseEnd_7798618] using wordTrace_append hprefix tailTrace_7798618
  have hstable : (prefixWord ++ tailWord_7798618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798618).length < 2 ^ (prefixWord ++ tailWord_7798618).sum := by decide
  have hdescent : baseEnd_7798618 < baseStart_7798618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798628 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_7798628 : Nat := 118140960795 + 7798628 * 2 ^ 59
def prefixEnd_7798628 : Nat := 4983230072969 + 3 ^ 40 * 7798628 * 2
def baseEnd_7798628 : Nat := 1334814869870539688594923

theorem tailTrace_7798628 : CollatzResearch.WordTrace tailWord_7798628 prefixEnd_7798628 1334814869870539688594923 := by
  unfold tailWord_7798628
  simp only [CollatzResearch.WordTrace]
  refine ⟨142219665395455065234782269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189626220527273420313043025 142219665395455065234782269)
  ·
    refine ⟨53332374523295649463043351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142219665395455065234782269 53332374523295649463043351)
    ·
      refine ⟨79998561784943474194565027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53332374523295649463043351 79998561784943474194565027)
      ·
        refine ⟨119997842677415211291847541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79998561784943474194565027 119997842677415211291847541)
        ·
          refine ⟨11249797751007676058610707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119997842677415211291847541 11249797751007676058610707)
          ·
            refine ⟨16874696626511514087916061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11249797751007676058610707 16874696626511514087916061)
            ·
              refine ⟨6328011234941817782968523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16874696626511514087916061 6328011234941817782968523)
              ·
                refine ⟨9492016852412726674452785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6328011234941817782968523 9492016852412726674452785)
                ·
                  refine ⟨7119012639309545005839589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9492016852412726674452785 7119012639309545005839589)
                  ·
                    refine ⟨1334814869870539688594923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119012639309545005839589 1334814869870539688594923)
                    ·
                      rfl

theorem cell23_7798628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_7798628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798628 prefixEnd_7798628 := by exact prefixLift 7798628
  have htrace : WordTrace (prefixWord ++ tailWord_7798628) baseStart_7798628 baseEnd_7798628 := by
    simpa [prefixWord, tailWord_7798628, baseEnd_7798628] using wordTrace_append hprefix tailTrace_7798628
  have hstable : (prefixWord ++ tailWord_7798628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798628).length < 2 ^ (prefixWord ++ tailWord_7798628).sum := by decide
  have hdescent : baseEnd_7798628 < baseStart_7798628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798637 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_7798637 : Nat := 118140960795 + 7798637 * 2 ^ 59
def prefixEnd_7798637 : Nat := 4983230072969 + 3 ^ 40 * 7798637 * 2
def baseEnd_7798637 : Nat := 1334816410312503176857409

theorem tailTrace_7798637 : CollatzResearch.WordTrace tailWord_7798637 prefixEnd_7798637 1334816410312503176857409 := by
  unfold tailWord_7798637
  simp only [CollatzResearch.WordTrace]
  refine ⟨284439659047877525006642165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189626439365251683337761443 284439659047877525006642165)
  ·
    refine ⟨26666218035738517969372703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284439659047877525006642165 26666218035738517969372703)
    ·
      refine ⟨39999327053607776954059055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26666218035738517969372703 39999327053607776954059055)
      ·
        refine ⟨59998990580411665431088583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39999327053607776954059055 59998990580411665431088583)
        ·
          refine ⟨89998485870617498146632875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59998990580411665431088583 89998485870617498146632875)
          ·
            refine ⟨134997728805926247219949313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89998485870617498146632875 134997728805926247219949313)
            ·
              refine ⟨101248296604444685414961985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134997728805926247219949313 101248296604444685414961985)
              ·
                refine ⟨75936222453333514061221489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101248296604444685414961985 75936222453333514061221489)
                ·
                  refine ⟨56952166840000135545916117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75936222453333514061221489 56952166840000135545916117)
                  ·
                    refine ⟨1334816410312503176857409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56952166840000135545916117 1334816410312503176857409)
                    ·
                      rfl

theorem cell23_7798637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_7798637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798637 prefixEnd_7798637 := by exact prefixLift 7798637
  have htrace : WordTrace (prefixWord ++ tailWord_7798637) baseStart_7798637 baseEnd_7798637 := by
    simpa [prefixWord, tailWord_7798637, baseEnd_7798637] using wordTrace_append hprefix tailTrace_7798637
  have hstable : (prefixWord ++ tailWord_7798637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798637).length < 2 ^ (prefixWord ++ tailWord_7798637).sum := by decide
  have hdescent : baseEnd_7798637 < baseStart_7798637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798638 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_7798638 : Nat := 118140960795 + 7798638 * 2 ^ 59
def prefixEnd_7798638 : Nat := 4983230072969 + 3 ^ 40 * 7798638 * 2
def baseEnd_7798638 : Nat := 4004449744418164026659723

theorem tailTrace_7798638 : CollatzResearch.WordTrace tailWord_7798638 prefixEnd_7798638 4004449744418164026659723 := by
  unfold tailWord_7798638
  simp only [CollatzResearch.WordTrace]
  refine ⟨35554961940109237772178571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189626463680582601451619045 35554961940109237772178571)
  ·
    refine ⟨53332442910163856658267857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35554961940109237772178571 53332442910163856658267857)
    ·
      refine ⟨39999332182622892493700893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53332442910163856658267857 39999332182622892493700893)
      ·
        refine ⟨14999749568483584685137835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39999332182622892493700893 14999749568483584685137835)
        ·
          refine ⟨22499624352725377027706753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14999749568483584685137835 22499624352725377027706753)
          ·
            refine ⟨16874718264544032770780065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22499624352725377027706753 16874718264544032770780065)
            ·
              refine ⟨12656038698408024578085049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16874718264544032770780065 12656038698408024578085049)
              ·
                refine ⟨9492029023806018433563787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12656038698408024578085049 9492029023806018433563787)
                ·
                  refine ⟨14238043535709027650345681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9492029023806018433563787 14238043535709027650345681)
                  ·
                    refine ⟨10678532651781770737759261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14238043535709027650345681 10678532651781770737759261)
                    ·
                      refine ⟨4004449744418164026659723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10678532651781770737759261 4004449744418164026659723)
                      ·
                        rfl

theorem cell23_7798638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_7798638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798638 prefixEnd_7798638 := by exact prefixLift 7798638
  have htrace : WordTrace (prefixWord ++ tailWord_7798638) baseStart_7798638 baseEnd_7798638 := by
    simpa [prefixWord, tailWord_7798638, baseEnd_7798638] using wordTrace_append hprefix tailTrace_7798638
  have hstable : (prefixWord ++ tailWord_7798638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798638).length < 2 ^ (prefixWord ++ tailWord_7798638).sum := by decide
  have hdescent : baseEnd_7798638 < baseStart_7798638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798661 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 1, 3, 2]
def baseStart_7798661 : Nat := 118140960795 + 7798661 * 2 ^ 59
def prefixEnd_7798661 : Nat := 4983230072969 + 3 ^ 40 * 7798661 * 2
def baseEnd_7798661 : Nat := 4004461554473217436672117

theorem tailTrace_7798661 : CollatzResearch.WordTrace tailWord_7798661 prefixEnd_7798661 4004461554473217436672117 := by
  unfold tailWord_7798661
  simp only [CollatzResearch.WordTrace]
  refine ⟨284440534399790577105515837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189627022933193718070343891 284440534399790577105515837)
  ·
    refine ⟨106665200399921466414568439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284440534399790577105515837 106665200399921466414568439)
    ·
      refine ⟨159997800599882199621852659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106665200399921466414568439 159997800599882199621852659)
      ·
        refine ⟨239996700899823299432778989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159997800599882199621852659 239996700899823299432778989)
        ·
          refine ⟨89998762837433737287292121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239996700899823299432778989 89998762837433737287292121)
          ·
            refine ⟨67499072128075302965469091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89998762837433737287292121 67499072128075302965469091)
            ·
              refine ⟨101248608192112954448203637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67499072128075302965469091 101248608192112954448203637)
              ·
                refine ⟨9492057018010589479519091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101248608192112954448203637 9492057018010589479519091)
                ·
                  refine ⟨14238085527015884219278637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9492057018010589479519091 14238085527015884219278637)
                  ·
                    refine ⟨5339282072630956582229489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14238085527015884219278637 5339282072630956582229489)
                    ·
                      refine ⟨4004461554473217436672117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339282072630956582229489 4004461554473217436672117)
                      ·
                        rfl

theorem cell23_7798661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_7798661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798661 prefixEnd_7798661 := by exact prefixLift 7798661
  have htrace : WordTrace (prefixWord ++ tailWord_7798661) baseStart_7798661 baseEnd_7798661 := by
    simpa [prefixWord, tailWord_7798661, baseEnd_7798661] using wordTrace_append hprefix tailTrace_7798661
  have hstable : (prefixWord ++ tailWord_7798661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798661).length < 2 ^ (prefixWord ++ tailWord_7798661).sum := by decide
  have hdescent : baseEnd_7798661 < baseStart_7798661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798677 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_7798677 : Nat := 118140960795 + 7798677 * 2 ^ 59
def prefixEnd_7798677 : Nat := 4983230072969 + 3 ^ 40 * 7798677 * 2
def baseEnd_7798677 : Nat := 4004469770163689374072043

theorem tailTrace_7798677 : CollatzResearch.WordTrace tailWord_7798677 prefixEnd_7798677 4004469770163689374072043 := by
  unfold tailWord_7798677
  simp only [CollatzResearch.WordTrace]
  refine ⟨284441117967732611838098285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189627411978488407892065523 284441117967732611838098285)
  ·
    refine ⟨106665419237899729439286857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284441117967732611838098285 106665419237899729439286857)
    ·
      refine ⟨79999064428424797079465143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106665419237899729439286857 79999064428424797079465143)
      ·
        refine ⟨119998596642637195619197715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79999064428424797079465143 119998596642637195619197715)
        ·
          refine ⟨179997894963955793428796573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119998596642637195619197715 179997894963955793428796573)
          ·
            refine ⟨67499210611483422535798715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179997894963955793428796573 67499210611483422535798715)
            ·
              refine ⟨101248815917225133803698073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67499210611483422535798715 101248815917225133803698073)
              ·
                refine ⟨75936611937918850352773555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101248815917225133803698073 75936611937918850352773555)
                ·
                  refine ⟨113904917906878275529160333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75936611937918850352773555 113904917906878275529160333)
                  ·
                    refine ⟨42714344215079353323435125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113904917906878275529160333 42714344215079353323435125)
                    ·
                      refine ⟨4004469770163689374072043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42714344215079353323435125 4004469770163689374072043)
                      ·
                        rfl

theorem cell23_7798677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_7798677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798677 prefixEnd_7798677 := by exact prefixLift 7798677
  have htrace : WordTrace (prefixWord ++ tailWord_7798677) baseStart_7798677 baseEnd_7798677 := by
    simpa [prefixWord, tailWord_7798677, baseEnd_7798677] using wordTrace_append hprefix tailTrace_7798677
  have hstable : (prefixWord ++ tailWord_7798677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798677).length < 2 ^ (prefixWord ++ tailWord_7798677).sum := by decide
  have hdescent : baseEnd_7798677 < baseStart_7798677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798685 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_7798685 : Nat := 118140960795 + 7798685 * 2 ^ 59
def prefixEnd_7798685 : Nat := 4983230072969 + 3 ^ 40 * 7798685 * 2
def baseEnd_7798685 : Nat := 4004473878008925342772007

theorem tailTrace_7798685 : CollatzResearch.WordTrace tailWord_7798685 prefixEnd_7798685 4004473878008925342772007 := by
  unfold tailWord_7798685
  simp only [CollatzResearch.WordTrace]
  refine ⟨284441409751703629204389509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189627606501135752802926339 284441409751703629204389509)
  ·
    refine ⟨53332764328444430475823033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284441409751703629204389509 53332764328444430475823033)
    ·
      refine ⟨39999573246333322856867275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53332764328444430475823033 39999573246333322856867275)
      ·
        refine ⟨59999359869499984285300913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39999573246333322856867275 59999359869499984285300913)
        ·
          refine ⟨44999519902124988213975685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59999359869499984285300913 44999519902124988213975685)
          ·
            refine ⟨8437409981648435290120441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44999519902124988213975685 8437409981648435290120441)
            ·
              refine ⟨6328057486236326467590331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8437409981648435290120441 6328057486236326467590331)
              ·
                refine ⟨9492086229354489701385497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6328057486236326467590331 9492086229354489701385497)
                ·
                  refine ⟨7119064672015867276039123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9492086229354489701385497 7119064672015867276039123)
                  ·
                    refine ⟨10678597008023800914058685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7119064672015867276039123 10678597008023800914058685)
                    ·
                      refine ⟨4004473878008925342772007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10678597008023800914058685 4004473878008925342772007)
                      ·
                        rfl

theorem cell23_7798685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_7798685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798685 prefixEnd_7798685 := by exact prefixLift 7798685
  have htrace : WordTrace (prefixWord ++ tailWord_7798685) baseStart_7798685 baseEnd_7798685 := by
    simpa [prefixWord, tailWord_7798685, baseEnd_7798685] using wordTrace_append hprefix tailTrace_7798685
  have hstable : (prefixWord ++ tailWord_7798685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798685).length < 2 ^ (prefixWord ++ tailWord_7798685).sum := by decide
  have hdescent : baseEnd_7798685 < baseStart_7798685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798695 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_7798695 : Nat := 118140960795 + 7798695 * 2 ^ 59
def prefixEnd_7798695 : Nat := 4983230072969 + 3 ^ 40 * 7798695 * 2
def baseEnd_7798695 : Nat := 4004479012815470303646961

theorem tailTrace_7798695 : CollatzResearch.WordTrace tailWord_7798695 prefixEnd_7798695 4004479012815470303646961 := by
  unfold tailWord_7798695
  simp only [CollatzResearch.WordTrace]
  refine ⟨284441774481667400912253539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189627849654444933941502359 284441774481667400912253539)
  ·
    refine ⟨426662661722501101368380309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284441774481667400912253539 426662661722501101368380309)
    ·
      refine ⟨19999812268242239126642827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 426662661722501101368380309 19999812268242239126642827)
      ·
        refine ⟨29999718402363358689964241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19999812268242239126642827 29999718402363358689964241)
        ·
          refine ⟨22499788801772519017473181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29999718402363358689964241 22499788801772519017473181)
          ·
            refine ⟨8437420800664694631552443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22499788801772519017473181 8437420800664694631552443)
            ·
              refine ⟨12656131200997041947328665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8437420800664694631552443 12656131200997041947328665)
              ·
                refine ⟨9492098400747781460496499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12656131200997041947328665 9492098400747781460496499)
                ·
                  refine ⟨14238147601121672190744749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9492098400747781460496499 14238147601121672190744749)
                  ·
                    refine ⟨5339305350420627071529281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14238147601121672190744749 5339305350420627071529281)
                    ·
                      refine ⟨4004479012815470303646961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339305350420627071529281 4004479012815470303646961)
                      ·
                        rfl

theorem cell23_7798695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_7798695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798695 prefixEnd_7798695 := by exact prefixLift 7798695
  have htrace : WordTrace (prefixWord ++ tailWord_7798695) baseStart_7798695 baseEnd_7798695 := by
    simpa [prefixWord, tailWord_7798695, baseEnd_7798695] using wordTrace_append hprefix tailTrace_7798695
  have hstable : (prefixWord ++ tailWord_7798695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798695).length < 2 ^ (prefixWord ++ tailWord_7798695).sum := by decide
  have hdescent : baseEnd_7798695 < baseStart_7798695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798727 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 3, 7]
def baseStart_7798727 : Nat := 118140960795 + 7798727 * 2 ^ 59
def prefixEnd_7798727 : Nat := 4983230072969 + 3 ^ 40 * 7798727 * 2
def baseEnd_7798727 : Nat := 1334831814732138059482271

theorem tailTrace_7798727 : CollatzResearch.WordTrace tailWord_7798727 prefixEnd_7798727 1334831814732138059482271 := by
  unfold tailWord_7798727
  simp only [CollatzResearch.WordTrace]
  refine ⟨284442941617551470377418435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189628627745034313584945623 284442941617551470377418435)
  ·
    refine ⟨426664412426327205566127653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284442941617551470377418435 426664412426327205566127653)
    ·
      refine ⟨79999577329936351043648935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426664412426327205566127653 79999577329936351043648935)
      ·
        refine ⟨119999365994904526565473403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79999577329936351043648935 119999365994904526565473403)
        ·
          refine ⟨179999048992356789848210105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119999365994904526565473403 179999048992356789848210105)
          ·
            refine ⟨134999286744267592386157579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179999048992356789848210105 134999286744267592386157579)
            ·
              refine ⟨202498930116401388579236369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134999286744267592386157579 202498930116401388579236369)
              ·
                refine ⟨151874197587301041434427277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202498930116401388579236369 151874197587301041434427277)
                ·
                  refine ⟨56952824095237890537910229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151874197587301041434427277 56952824095237890537910229)
                  ·
                    refine ⟨1334831814732138059482271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56952824095237890537910229 1334831814732138059482271)
                    ·
                      rfl

theorem cell23_7798727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_7798727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798727 prefixEnd_7798727 := by exact prefixLift 7798727
  have htrace : WordTrace (prefixWord ++ tailWord_7798727) baseStart_7798727 baseEnd_7798727 := by
    simpa [prefixWord, tailWord_7798727, baseEnd_7798727] using wordTrace_append hprefix tailTrace_7798727
  have hstable : (prefixWord ++ tailWord_7798727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798727).length < 2 ^ (prefixWord ++ tailWord_7798727).sum := by decide
  have hdescent : baseEnd_7798727 < baseStart_7798727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798737 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_7798737 : Nat := 118140960795 + 7798737 * 2 ^ 59
def prefixEnd_7798737 : Nat := 4983230072969 + 3 ^ 40 * 7798737 * 2
def baseEnd_7798737 : Nat := 4004500579002959139321767

theorem tailTrace_7798737 : CollatzResearch.WordTrace tailWord_7798737 prefixEnd_7798737 4004500579002959139321767 := by
  unfold tailWord_7798737
  simp only [CollatzResearch.WordTrace]
  refine ⟨284443306347515242085282465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189628870898343494723521643 284443306347515242085282465)
  ·
    refine ⟨213332479760636431563961849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284443306347515242085282465 213332479760636431563961849)
    ·
      refine ⟨159999359820477323672971387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213332479760636431563961849 159999359820477323672971387)
      ·
        refine ⟨239999039730715985509457081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159999359820477323672971387 239999039730715985509457081)
        ·
          refine ⟨179999279798036989132092811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239999039730715985509457081 179999279798036989132092811)
          ·
            refine ⟨269998919697055483698139217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179999279798036989132092811 269998919697055483698139217)
            ·
              refine ⟨202499189772791612773604413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269998919697055483698139217 202499189772791612773604413)
              ·
                refine ⟨75937196164796854790101655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202499189772791612773604413 75937196164796854790101655)
                ·
                  refine ⟨113905794247195282185152483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75937196164796854790101655 113905794247195282185152483)
                  ·
                    refine ⟨170858691370792923277728725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113905794247195282185152483 170858691370792923277728725)
                    ·
                      refine ⟨4004500579002959139321767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170858691370792923277728725 4004500579002959139321767)
                      ·
                        rfl

theorem cell23_7798737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_7798737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798737 prefixEnd_7798737 := by exact prefixLift 7798737
  have htrace : WordTrace (prefixWord ++ tailWord_7798737) baseStart_7798737 baseEnd_7798737 := by
    simpa [prefixWord, tailWord_7798737, baseEnd_7798737] using wordTrace_append hprefix tailTrace_7798737
  have hstable : (prefixWord ++ tailWord_7798737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798737).length < 2 ^ (prefixWord ++ tailWord_7798737).sum := by decide
  have hdescent : baseEnd_7798737 < baseStart_7798737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798741 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7798741 : Nat := 118140960795 + 7798741 * 2 ^ 59
def prefixEnd_7798741 : Nat := 4983230072969 + 3 ^ 40 * 7798741 * 2
def baseEnd_7798741 : Nat := 4004502632925577123671749

theorem tailTrace_7798741 : CollatzResearch.WordTrace tailWord_7798741 prefixEnd_7798741 4004502632925577123671749 := by
  unfold tailWord_7798741
  simp only [CollatzResearch.WordTrace]
  refine ⟨284443452239500750768428077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189628968159667167178952051 284443452239500750768428077)
  ·
    refine ⟨106666294589812781538160529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284443452239500750768428077 106666294589812781538160529)
    ·
      refine ⟨79999720942359586153620397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106666294589812781538160529 79999720942359586153620397)
      ·
        refine ⟨29999895353384844807607649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79999720942359586153620397 29999895353384844807607649)
        ·
          refine ⟨22499921515038633605705737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29999895353384844807607649 22499921515038633605705737)
          ·
            refine ⟨16874941136278975204279303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22499921515038633605705737 16874941136278975204279303)
            ·
              refine ⟨25312411704418462806418955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16874941136278975204279303 25312411704418462806418955)
              ·
                refine ⟨37968617556627694209628433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25312411704418462806418955 37968617556627694209628433)
                ·
                  refine ⟨28476463167470770657221325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37968617556627694209628433 28476463167470770657221325)
                  ·
                    refine ⟨10678673687801538996457997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28476463167470770657221325 10678673687801538996457997)
                    ·
                      refine ⟨4004502632925577123671749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10678673687801538996457997 4004502632925577123671749)
                      ·
                        rfl

theorem cell23_7798741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7798741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798741 prefixEnd_7798741 := by exact prefixLift 7798741
  have htrace : WordTrace (prefixWord ++ tailWord_7798741) baseStart_7798741 baseEnd_7798741 := by
    simpa [prefixWord, tailWord_7798741, baseEnd_7798741] using wordTrace_append hprefix tailTrace_7798741
  have hstable : (prefixWord ++ tailWord_7798741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798741).length < 2 ^ (prefixWord ++ tailWord_7798741).sum := by decide
  have hdescent : baseEnd_7798741 < baseStart_7798741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798765 : List Nat := [1, 5, 1, 4, 1, 1, 2, 3, 5]
def baseStart_7798765 : Nat := 118140960795 + 7798765 * 2 ^ 59
def prefixEnd_7798765 : Nat := 4983230072969 + 3 ^ 40 * 7798765 * 2
def baseEnd_7798765 : Nat := 444946106273476114419071

theorem tailTrace_7798765 : CollatzResearch.WordTrace tailWord_7798765 prefixEnd_7798765 444946106273476114419071 := by
  unfold tailWord_7798765
  simp only [CollatzResearch.WordTrace]
  refine ⟨284444327591413802867301749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189629551727609201911534499 284444327591413802867301749)
  ·
    refine ⟨26666655711695044018809539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284444327591413802867301749 26666655711695044018809539)
    ·
      refine ⟨39999983567542566028214309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26666655711695044018809539 39999983567542566028214309)
      ·
        refine ⟨7499996918914231130290183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39999983567542566028214309 7499996918914231130290183)
        ·
          refine ⟨11249995378371346695435275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7499996918914231130290183 11249995378371346695435275)
          ·
            refine ⟨16874993067557020043152913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11249995378371346695435275 16874993067557020043152913)
            ·
              refine ⟨12656244800667765032364685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16874993067557020043152913 12656244800667765032364685)
              ·
                refine ⟨4746091800250411887136757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12656244800667765032364685 4746091800250411887136757)
                ·
                  refine ⟨444946106273476114419071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4746091800250411887136757 444946106273476114419071)
                  ·
                    rfl

theorem cell23_7798765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_7798765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798765 prefixEnd_7798765 := by exact prefixLift 7798765
  have htrace : WordTrace (prefixWord ++ tailWord_7798765) baseStart_7798765 baseEnd_7798765 := by
    simpa [prefixWord, tailWord_7798765, baseEnd_7798765] using wordTrace_append hprefix tailTrace_7798765
  have hstable : (prefixWord ++ tailWord_7798765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798765).length < 2 ^ (prefixWord ++ tailWord_7798765).sum := by decide
  have hdescent : baseEnd_7798765 < baseStart_7798765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798781 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_7798781 : Nat := 118140960795 + 7798781 * 2 ^ 59
def prefixEnd_7798781 : Nat := 4983230072969 + 3 ^ 40 * 7798781 * 2
def baseEnd_7798781 : Nat := 4004523172151756967171565

theorem tailTrace_7798781 : CollatzResearch.WordTrace tailWord_7798781 prefixEnd_7798781 4004523172151756967171565 := by
  unfold tailWord_7798781
  simp only [CollatzResearch.WordTrace]
  refine ⟨284444911159355837599884197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189629940772903891733256131 284444911159355837599884197)
  ·
    refine ⟨53333420842379219549978287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284444911159355837599884197 53333420842379219549978287)
    ·
      refine ⟨80000131263568829324967431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53333420842379219549978287 80000131263568829324967431)
      ·
        refine ⟨120000196895353243987451147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80000131263568829324967431 120000196895353243987451147)
        ·
          refine ⟨180000295343029865981176721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120000196895353243987451147 180000295343029865981176721)
          ·
            refine ⟨135000221507272399485882541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180000295343029865981176721 135000221507272399485882541)
            ·
              refine ⟨50625083065227149807205953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135000221507272399485882541 50625083065227149807205953)
              ·
                refine ⟨37968812298920362355404465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50625083065227149807205953 37968812298920362355404465)
                ·
                  refine ⟨28476609224190271766553349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37968812298920362355404465 28476609224190271766553349)
                  ·
                    refine ⟨5339364229535675956228753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28476609224190271766553349 5339364229535675956228753)
                    ·
                      refine ⟨4004523172151756967171565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339364229535675956228753 4004523172151756967171565)
                      ·
                        rfl

theorem cell23_7798781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_7798781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798781 prefixEnd_7798781 := by exact prefixLift 7798781
  have htrace : WordTrace (prefixWord ++ tailWord_7798781) baseStart_7798781 baseEnd_7798781 := by
    simpa [prefixWord, tailWord_7798781, baseEnd_7798781] using wordTrace_append hprefix tailTrace_7798781
  have hstable : (prefixWord ++ tailWord_7798781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798781).length < 2 ^ (prefixWord ++ tailWord_7798781).sum := by decide
  have hdescent : baseEnd_7798781 < baseStart_7798781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798791 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 3, 4]
def baseStart_7798791 : Nat := 118140960795 + 7798791 * 2 ^ 59
def prefixEnd_7798791 : Nat := 4983230072969 + 3 ^ 40 * 7798791 * 2
def baseEnd_7798791 : Nat := 1334842768986100642682173

theorem tailTrace_7798791 : CollatzResearch.WordTrace tailWord_7798791 prefixEnd_7798791 1334842768986100642682173 := by
  unfold tailWord_7798791
  simp only [CollatzResearch.WordTrace]
  refine ⟨284445275889319609307748227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189630183926213072871832151 284445275889319609307748227)
  ·
    refine ⟨426667913833979413961622341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284445275889319609307748227 426667913833979413961622341)
    ·
      refine ⟨80000233843871140117804189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426667913833979413961622341 80000233843871140117804189)
      ·
        refine ⟨30000087691451677544176571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80000233843871140117804189 30000087691451677544176571)
        ·
          refine ⟨45000131537177516316264857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30000087691451677544176571 45000131537177516316264857)
          ·
            refine ⟨33750098652883137237198643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45000131537177516316264857 33750098652883137237198643)
            ·
              refine ⟨50625147979324705855797965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33750098652883137237198643 50625147979324705855797965)
              ·
                refine ⟨18984430492246764695924237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50625147979324705855797965 18984430492246764695924237)
                ·
                  refine ⟨7119161434592536760971589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18984430492246764695924237 7119161434592536760971589)
                  ·
                    refine ⟨1334842768986100642682173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119161434592536760971589 1334842768986100642682173)
                    ·
                      rfl

theorem cell23_7798791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_7798791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798791 prefixEnd_7798791 := by exact prefixLift 7798791
  have htrace : WordTrace (prefixWord ++ tailWord_7798791) baseStart_7798791 baseEnd_7798791 := by
    simpa [prefixWord, tailWord_7798791, baseEnd_7798791] using wordTrace_append hprefix tailTrace_7798791
  have hstable : (prefixWord ++ tailWord_7798791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798791).length < 2 ^ (prefixWord ++ tailWord_7798791).sum := by decide
  have hdescent : baseEnd_7798791 < baseStart_7798791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798848 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 3, 1, 3]
def baseStart_7798848 : Nat := 118140960795 + 7798848 * 2 ^ 59
def prefixEnd_7798848 : Nat := 4983230072969 + 3 ^ 40 * 7798848 * 2
def baseEnd_7798848 : Nat := 4004557575355608205033757

theorem tailTrace_7798848 : CollatzResearch.WordTrace tailWord_7798848 prefixEnd_7798848 4004557575355608205033757 := by
  unfold tailWord_7798848
  simp only [CollatzResearch.WordTrace]
  refine ⟨142223677425056554021286599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189631569900075405361715465 142223677425056554021286599)
  ·
    refine ⟨213335516137584831031929899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142223677425056554021286599 213335516137584831031929899)
    ·
      refine ⟨320003274206377246547894849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213335516137584831031929899 320003274206377246547894849)
      ·
        refine ⟨240002455654782934910921137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320003274206377246547894849 240002455654782934910921137)
        ·
          refine ⟨180001841741087201183190853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240002455654782934910921137 180001841741087201183190853)
          ·
            refine ⟨33750345326453850221848285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180001841741087201183190853 33750345326453850221848285)
            ·
              refine ⟨12656379497420193833193107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33750345326453850221848285 12656379497420193833193107)
              ·
                refine ⟨18984569246130290749789661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12656379497420193833193107 18984569246130290749789661)
                ·
                  refine ⟨7119213467298859031171123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18984569246130290749789661 7119213467298859031171123)
                  ·
                    refine ⟨10678820200948288546756685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7119213467298859031171123 10678820200948288546756685)
                    ·
                      refine ⟨4004557575355608205033757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10678820200948288546756685 4004557575355608205033757)
                      ·
                        rfl

theorem cell23_7798848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_7798848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798848 prefixEnd_7798848 := by exact prefixLift 7798848
  have htrace : WordTrace (prefixWord ++ tailWord_7798848) baseStart_7798848 baseEnd_7798848 := by
    simpa [prefixWord, tailWord_7798848, baseEnd_7798848] using wordTrace_append hprefix tailTrace_7798848
  have hstable : (prefixWord ++ tailWord_7798848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798848).length < 2 ^ (prefixWord ++ tailWord_7798848).sum := by decide
  have hdescent : baseEnd_7798848 < baseStart_7798848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798871 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 2, 6, 2]
def baseStart_7798871 : Nat := 118140960795 + 7798871 * 2 ^ 59
def prefixEnd_7798871 : Nat := 4983230072969 + 3 ^ 40 * 7798871 * 2
def baseEnd_7798871 : Nat := 4004569385410661615046151

theorem tailTrace_7798871 : CollatzResearch.WordTrace tailWord_7798871 prefixEnd_7798871 4004569385410661615046151 := by
  unfold tailWord_7798871
  simp only [CollatzResearch.WordTrace]
  refine ⟨284448193729029782970660467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189632129152686521980440311 284448193729029782970660467)
  ·
    refine ⟨426672290593544674455990701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284448193729029782970660467 426672290593544674455990701)
    ·
      refine ⟨160002108972579252920996513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426672290593544674455990701 160002108972579252920996513)
      ·
        refine ⟨120001581729434439690747385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160002108972579252920996513 120001581729434439690747385)
        ·
          refine ⟨90001186297075829768060539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120001581729434439690747385 90001186297075829768060539)
          ·
            refine ⟨135001779445613744652090809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90001186297075829768060539 135001779445613744652090809)
            ·
              refine ⟨101251334584210308489068107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135001779445613744652090809 101251334584210308489068107)
              ·
                refine ⟨151877001876315462733602161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101251334584210308489068107 151877001876315462733602161)
                ·
                  refine ⟨113907751407236597050201621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151877001876315462733602161 113907751407236597050201621)
                  ·
                    refine ⟨5339425847214215486728201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113907751407236597050201621 5339425847214215486728201)
                    ·
                      refine ⟨4004569385410661615046151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339425847214215486728201 4004569385410661615046151)
                      ·
                        rfl

theorem cell23_7798871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_7798871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798871 prefixEnd_7798871 := by exact prefixLift 7798871
  have htrace : WordTrace (prefixWord ++ tailWord_7798871) baseStart_7798871 baseEnd_7798871 := by
    simpa [prefixWord, tailWord_7798871, baseEnd_7798871] using wordTrace_append hprefix tailTrace_7798871
  have hstable : (prefixWord ++ tailWord_7798871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798871).length < 2 ^ (prefixWord ++ tailWord_7798871).sum := by decide
  have hdescent : baseEnd_7798871 < baseStart_7798871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798898 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_7798898 : Nat := 118140960795 + 7798898 * 2 ^ 59
def prefixEnd_7798898 : Nat := 4983230072969 + 3 ^ 40 * 7798898 * 2
def baseEnd_7798898 : Nat := 1334861083129444336469509

theorem tailTrace_7798898 : CollatzResearch.WordTrace tailWord_7798898 prefixEnd_7798898 1334861083129444336469509 := by
  unfold tailWord_7798898
  simp only [CollatzResearch.WordTrace]
  refine ⟨71112294624982991645473337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189632785666621311054595565 71112294624982991645473337)
  ·
    refine ⟨53334220968737243734105003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71112294624982991645473337 53334220968737243734105003)
    ·
      refine ⟨80001331453105865601157505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53334220968737243734105003 80001331453105865601157505)
      ·
        refine ⟨60000998589829399200868129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80001331453105865601157505 60000998589829399200868129)
        ·
          refine ⟨45000748942372049400651097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60000998589829399200868129 45000748942372049400651097)
          ·
            refine ⟨33750561706779037050488323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45000748942372049400651097 33750561706779037050488323)
            ·
              refine ⟨50625842560168555575732485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33750561706779037050488323 50625842560168555575732485)
              ·
                refine ⟨9492345480031604170449841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50625842560168555575732485 9492345480031604170449841)
                ·
                  refine ⟨7119259110023703127837381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9492345480031604170449841 7119259110023703127837381)
                  ·
                    refine ⟨1334861083129444336469509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119259110023703127837381 1334861083129444336469509)
                    ·
                      rfl

theorem cell23_7798898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_7798898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798898 prefixEnd_7798898 := by exact prefixLift 7798898
  have htrace : WordTrace (prefixWord ++ tailWord_7798898) baseStart_7798898 baseEnd_7798898 := by
    simpa [prefixWord, tailWord_7798898, baseEnd_7798898] using wordTrace_append hprefix tailTrace_7798898
  have hstable : (prefixWord ++ tailWord_7798898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798898).length < 2 ^ (prefixWord ++ tailWord_7798898).sum := by decide
  have hdescent : baseEnd_7798898 < baseStart_7798898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798942 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7798942 : Nat := 118140960795 + 7798942 * 2 ^ 59
def prefixEnd_7798942 : Nat := 4983230072969 + 3 ^ 40 * 7798942 * 2
def baseEnd_7798942 : Nat := 4004605842537130837258325

theorem tailTrace_7798942 : CollatzResearch.WordTrace tailWord_7798942 prefixEnd_7798942 4004605842537130837258325 := by
  unfold tailWord_7798942
  simp only [CollatzResearch.WordTrace]
  refine ⟨35556347913971570262061885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189633855541181708064330053 35556347913971570262061885)
  ·
    refine ⟨13333630467739338848273207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35556347913971570262061885 13333630467739338848273207)
    ·
      refine ⟨20000445701609008272409811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333630467739338848273207 20000445701609008272409811)
      ·
        refine ⟨30000668552413512408614717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20000445701609008272409811 30000668552413512408614717)
        ·
          refine ⟨11250250707155067153230519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30000668552413512408614717 11250250707155067153230519)
          ·
            refine ⟨16875376060732600729845779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11250250707155067153230519 16875376060732600729845779)
            ·
              refine ⟨25313064091098901094768669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16875376060732600729845779 25313064091098901094768669)
              ·
                refine ⟨9492399034162087910538251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25313064091098901094768669 9492399034162087910538251)
                ·
                  refine ⟨14238598551243131865807377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9492399034162087910538251 14238598551243131865807377)
                  ·
                    refine ⟨10678948913432348899355533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14238598551243131865807377 10678948913432348899355533)
                    ·
                      refine ⟨4004605842537130837258325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10678948913432348899355533 4004605842537130837258325)
                      ·
                        rfl

theorem cell23_7798942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7798942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798942 prefixEnd_7798942 := by exact prefixLift 7798942
  have htrace : WordTrace (prefixWord ++ tailWord_7798942) baseStart_7798942 baseEnd_7798942 := by
    simpa [prefixWord, tailWord_7798942, baseEnd_7798942] using wordTrace_append hprefix tailTrace_7798942
  have hstable : (prefixWord ++ tailWord_7798942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798942).length < 2 ^ (prefixWord ++ tailWord_7798942).sum := by decide
  have hdescent : baseEnd_7798942 < baseStart_7798942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798972 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_7798972 : Nat := 118140960795 + 7798972 * 2 ^ 59
def prefixEnd_7798972 : Nat := 4983230072969 + 3 ^ 40 * 7798972 * 2
def baseEnd_7798972 : Nat := 4004621246956765719883187

theorem tailTrace_7798972 : CollatzResearch.WordTrace tailWord_7798972 prefixEnd_7798972 4004621246956765719883187 := by
  unfold tailWord_7798972
  simp only [CollatzResearch.WordTrace]
  refine ⟨142225938750831938610043585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189634585001109251480058113 142225938750831938610043585)
  ·
    refine ⟨106669454063123953957532689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142225938750831938610043585 106669454063123953957532689)
    ·
      refine ⟨80002090547342965468149517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106669454063123953957532689 80002090547342965468149517)
      ·
        refine ⟨30000783955253612050556069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80002090547342965468149517 30000783955253612050556069)
        ·
          refine ⟨5625146991610052259479263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30000783955253612050556069 5625146991610052259479263)
          ·
            refine ⟨8437720487415078389218895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625146991610052259479263 8437720487415078389218895)
            ·
              refine ⟨12656580731122617583828343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8437720487415078389218895 12656580731122617583828343)
              ·
                refine ⟨18984871096683926375742515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12656580731122617583828343 18984871096683926375742515)
                ·
                  refine ⟨28477306645025889563613773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18984871096683926375742515 28477306645025889563613773)
                  ·
                    refine ⟨10678989991884708586355165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28477306645025889563613773 10678989991884708586355165)
                    ·
                      refine ⟨4004621246956765719883187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10678989991884708586355165 4004621246956765719883187)
                      ·
                        rfl

theorem cell23_7798972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_7798972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798972 prefixEnd_7798972 := by exact prefixLift 7798972
  have htrace : WordTrace (prefixWord ++ tailWord_7798972) baseStart_7798972 baseEnd_7798972 := by
    simpa [prefixWord, tailWord_7798972, baseEnd_7798972] using wordTrace_append hprefix tailTrace_7798972
  have hstable : (prefixWord ++ tailWord_7798972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798972).length < 2 ^ (prefixWord ++ tailWord_7798972).sum := by decide
  have hdescent : baseEnd_7798972 < baseStart_7798972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798981 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_7798981 : Nat := 118140960795 + 7798981 * 2 ^ 59
def prefixEnd_7798981 : Nat := 4983230072969 + 3 ^ 40 * 7798981 * 2
def baseEnd_7798981 : Nat := 4004625868282656184670645

theorem tailTrace_7798981 : CollatzResearch.WordTrace tailWord_7798981 prefixEnd_7798981 4004625868282656184670645 := by
  unfold tailWord_7798981
  simp only [CollatzResearch.WordTrace]
  refine ⟨284452205758631271757164797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189634803839087514504776531 284452205758631271757164797)
  ·
    refine ⟨106669577159486726908936799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284452205758631271757164797 106669577159486726908936799)
    ·
      refine ⟨160004365739230090363405199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106669577159486726908936799 160004365739230090363405199)
      ·
        refine ⟨240006548608845135545107799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160004365739230090363405199 240006548608845135545107799)
        ·
          refine ⟨360009822913267703317661699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240006548608845135545107799 360009822913267703317661699)
          ·
            refine ⟨540014734369901554976492549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360009822913267703317661699 540014734369901554976492549)
            ·
              refine ⟨101252762694356541558092353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540014734369901554976492549 101252762694356541558092353)
              ·
                refine ⟨75939572020767406168569265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101252762694356541558092353 75939572020767406168569265)
                ·
                  refine ⟨56954679015575554626426949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75939572020767406168569265 56954679015575554626426949)
                  ·
                    refine ⟨10679002315420416492455053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56954679015575554626426949 10679002315420416492455053)
                    ·
                      refine ⟨4004625868282656184670645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679002315420416492455053 4004625868282656184670645)
                      ·
                        rfl

theorem cell23_7798981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_7798981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7798981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7798981 prefixEnd_7798981 := by exact prefixLift 7798981
  have htrace : WordTrace (prefixWord ++ tailWord_7798981) baseStart_7798981 baseEnd_7798981 := by
    simpa [prefixWord, tailWord_7798981, baseEnd_7798981] using wordTrace_append hprefix tailTrace_7798981
  have hstable : (prefixWord ++ tailWord_7798981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798981).length < 2 ^ (prefixWord ++ tailWord_7798981).sum := by decide
  have hdescent : baseEnd_7798981 < baseStart_7798981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799041 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_7799041 : Nat := 118140960795 + 7799041 * 2 ^ 59
def prefixEnd_7799041 : Nat := 4983230072969 + 3 ^ 40 * 7799041 * 2
def baseEnd_7799041 : Nat := 4004656677121925949920369

theorem tailTrace_7799041 : CollatzResearch.WordTrace tailWord_7799041 prefixEnd_7799041 4004656677121925949920369 := by
  unfold tailWord_7799041
  simp only [CollatzResearch.WordTrace]
  refine ⟨284454394138413902004348977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189636262758942601336232651 284454394138413902004348977)
  ·
    refine ⟨213340795603810426503261733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284454394138413902004348977 213340795603810426503261733)
    ·
      refine ⟨40001399175714454969361575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213340795603810426503261733 40001399175714454969361575)
      ·
        refine ⟨60002098763571682454042363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40001399175714454969361575 60002098763571682454042363)
        ·
          refine ⟨90003148145357523681063545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60002098763571682454042363 90003148145357523681063545)
          ·
            refine ⟨67502361109018142760797659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90003148145357523681063545 67502361109018142760797659)
            ·
              refine ⟨101253541663527214141196489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67502361109018142760797659 101253541663527214141196489)
              ·
                refine ⟨75940156247645410605897367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101253541663527214141196489 75940156247645410605897367)
                ·
                  refine ⟨113910234371468115908846051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75940156247645410605897367 113910234371468115908846051)
                  ·
                    refine ⟨170865351557202173863269077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113910234371468115908846051 170865351557202173863269077)
                    ·
                      refine ⟨4004656677121925949920369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170865351557202173863269077 4004656677121925949920369)
                      ·
                        rfl

theorem cell23_7799041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_7799041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799041 prefixEnd_7799041 := by exact prefixLift 7799041
  have htrace : WordTrace (prefixWord ++ tailWord_7799041) baseStart_7799041 baseEnd_7799041 := by
    simpa [prefixWord, tailWord_7799041, baseEnd_7799041] using wordTrace_append hprefix tailTrace_7799041
  have hstable : (prefixWord ++ tailWord_7799041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799041).length < 2 ^ (prefixWord ++ tailWord_7799041).sum := by decide
  have hdescent : baseEnd_7799041 < baseStart_7799041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799048 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 2, 5]
def baseStart_7799048 : Nat := 118140960795 + 7799048 * 2 ^ 59
def prefixEnd_7799048 : Nat := 4983230072969 + 3 ^ 40 * 7799048 * 2
def baseEnd_7799048 : Nat := 1334886757162169140844279

theorem tailTrace_7799048 : CollatzResearch.WordTrace tailWord_7799048 prefixEnd_7799048 1334886757162169140844279 := by
  unfold tailWord_7799048
  simp only [CollatzResearch.WordTrace]
  refine ⟨142227324724694271099926899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189636432966259028133235865 142227324724694271099926899)
  ·
    refine ⟨213340987087041406649890349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142227324724694271099926899 213340987087041406649890349)
    ·
      refine ⟨80002870157640527493708881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213340987087041406649890349 80002870157640527493708881)
      ·
        refine ⟨60002152618230395620281661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80002870157640527493708881 60002152618230395620281661)
        ·
          refine ⟨22500807231836398357605623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60002152618230395620281661 22500807231836398357605623)
          ·
            refine ⟨33751210847754597536408435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22500807231836398357605623 33751210847754597536408435)
            ·
              refine ⟨50626816271631896304612653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33751210847754597536408435 50626816271631896304612653)
              ·
                refine ⟨18985056101861961114229745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50626816271631896304612653 18985056101861961114229745)
                ·
                  refine ⟨14238792076396470835672309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18985056101861961114229745 14238792076396470835672309)
                  ·
                    refine ⟨1334886757162169140844279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14238792076396470835672309 1334886757162169140844279)
                    ·
                      rfl

theorem cell23_7799048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_7799048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799048 prefixEnd_7799048 := by exact prefixLift 7799048
  have htrace : WordTrace (prefixWord ++ tailWord_7799048) baseStart_7799048 baseEnd_7799048 := by
    simpa [prefixWord, tailWord_7799048, baseEnd_7799048] using wordTrace_append hprefix tailTrace_7799048
  have hstable : (prefixWord ++ tailWord_7799048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799048).length < 2 ^ (prefixWord ++ tailWord_7799048).sum := by decide
  have hdescent : baseEnd_7799048 < baseStart_7799048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799069 : List Nat := [1, 4, 2, 3, 2, 2, 2, 2, 5]
def baseStart_7799069 : Nat := 118140960795 + 7799069 * 2 ^ 59
def prefixEnd_7799069 : Nat := 4983230072969 + 3 ^ 40 * 7799069 * 2
def baseEnd_7799069 : Nat := 444963450508916871152249

theorem tailTrace_7799069 : CollatzResearch.WordTrace tailWord_7799069 prefixEnd_7799069 444963450508916871152249 := by
  unfold tailWord_7799069
  simp only [CollatzResearch.WordTrace]
  refine ⟨284455415382312462786368261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189636943588208308524245507 284455415382312462786368261)
  ·
    refine ⟨53335390384183586772444049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284455415382312462786368261 53335390384183586772444049)
    ·
      refine ⟨40001542788137690079333037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53335390384183586772444049 40001542788137690079333037)
      ·
        refine ⟨15000578545551633779749889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40001542788137690079333037 15000578545551633779749889)
        ·
          refine ⟨11250433909163725334812417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15000578545551633779749889 11250433909163725334812417)
          ·
            refine ⟨8437825431872794001109313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11250433909163725334812417 8437825431872794001109313)
            ·
              refine ⟨6328369073904595500831985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8437825431872794001109313 6328369073904595500831985)
              ·
                refine ⟨4746276805428446625623989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6328369073904595500831985 4746276805428446625623989)
                ·
                  refine ⟨444963450508916871152249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4746276805428446625623989 444963450508916871152249)
                  ·
                    rfl

theorem cell23_7799069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_7799069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799069 prefixEnd_7799069 := by exact prefixLift 7799069
  have htrace : WordTrace (prefixWord ++ tailWord_7799069) baseStart_7799069 baseEnd_7799069 := by
    simpa [prefixWord, tailWord_7799069, baseEnd_7799069] using wordTrace_append hprefix tailTrace_7799069
  have hstable : (prefixWord ++ tailWord_7799069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799069).length < 2 ^ (prefixWord ++ tailWord_7799069).sum := by decide
  have hdescent : baseEnd_7799069 < baseStart_7799069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799079 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7799079 : Nat := 118140960795 + 7799079 * 2 ^ 59
def prefixEnd_7799079 : Nat := 4983230072969 + 3 ^ 40 * 7799079 * 2
def baseEnd_7799079 : Nat := 4004676189386796801245195

theorem tailTrace_7799079 : CollatzResearch.WordTrace tailWord_7799079 prefixEnd_7799079 4004676189386796801245195 := by
  unfold tailWord_7799079
  simp only [CollatzResearch.WordTrace]
  refine ⟨284455780112276234494232291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189637186741517489662821527 284455780112276234494232291)
  ·
    refine ⟨426683670168414351741348437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284455780112276234494232291 426683670168414351741348437)
    ·
      refine ⟨5000199259786105684468927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 426683670168414351741348437 5000199259786105684468927)
      ·
        refine ⟨7500298889679158526703391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000199259786105684468927 7500298889679158526703391)
        ·
          refine ⟨11250448334518737790055087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500298889679158526703391 11250448334518737790055087)
          ·
            refine ⟨16875672501778106685082631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11250448334518737790055087 16875672501778106685082631)
            ·
              refine ⟨25313508752667160027623947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16875672501778106685082631 25313508752667160027623947)
              ·
                refine ⟨37970263129000740041435921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25313508752667160027623947 37970263129000740041435921)
                ·
                  refine ⟨28477697346750555031076941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37970263129000740041435921 28477697346750555031076941)
                  ·
                    refine ⟨10679136505031458136653853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28477697346750555031076941 10679136505031458136653853)
                    ·
                      refine ⟨4004676189386796801245195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679136505031458136653853 4004676189386796801245195)
                      ·
                        rfl

theorem cell23_7799079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7799079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799079 prefixEnd_7799079 := by exact prefixLift 7799079
  have htrace : WordTrace (prefixWord ++ tailWord_7799079) baseStart_7799079 baseEnd_7799079 := by
    simpa [prefixWord, tailWord_7799079, baseEnd_7799079] using wordTrace_append hprefix tailTrace_7799079
  have hstable : (prefixWord ++ tailWord_7799079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799079).length < 2 ^ (prefixWord ++ tailWord_7799079).sum := by decide
  have hdescent : baseEnd_7799079 < baseStart_7799079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799102 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_7799102 : Nat := 118140960795 + 7799102 * 2 ^ 59
def prefixEnd_7799102 : Nat := 4983230072969 + 3 ^ 40 * 7799102 * 2
def baseEnd_7799102 : Nat := 4004687999441850211257589

theorem tailTrace_7799102 : CollatzResearch.WordTrace tailWord_7799102 prefixEnd_7799102 4004687999441850211257589 := by
  unfold tailWord_7799102
  simp only [CollatzResearch.WordTrace]
  refine ⟨35557077373899113677789945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189637745994128606281546373 35557077373899113677789945)
  ·
    refine ⟨26667808030424335258342459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35557077373899113677789945 26667808030424335258342459)
    ·
      refine ⟨40001712045636502887513689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26667808030424335258342459 40001712045636502887513689)
      ·
        refine ⟨30001284034227377165635267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40001712045636502887513689 30001284034227377165635267)
        ·
          refine ⟨45001926051341065748452901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30001284034227377165635267 45001926051341065748452901)
          ·
            refine ⟨8437861134626449827834919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45001926051341065748452901 8437861134626449827834919)
            ·
              refine ⟨12656791701939674741752379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8437861134626449827834919 12656791701939674741752379)
              ·
                refine ⟨18985187552909512112628569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12656791701939674741752379 18985187552909512112628569)
                ·
                  refine ⟨14238890664682134084471427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18985187552909512112628569 14238890664682134084471427)
                  ·
                    refine ⟨21358335997023201126707141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14238890664682134084471427 21358335997023201126707141)
                    ·
                      refine ⟨4004687999441850211257589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21358335997023201126707141 4004687999441850211257589)
                      ·
                        rfl

theorem cell23_7799102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_7799102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799102 prefixEnd_7799102 := by exact prefixLift 7799102
  have htrace : WordTrace (prefixWord ++ tailWord_7799102) baseStart_7799102 baseEnd_7799102 := by
    simpa [prefixWord, tailWord_7799102, baseEnd_7799102] using wordTrace_append hprefix tailTrace_7799102
  have hstable : (prefixWord ++ tailWord_7799102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799102).length < 2 ^ (prefixWord ++ tailWord_7799102).sum := by decide
  have hdescent : baseEnd_7799102 < baseStart_7799102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799135 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 3]
def baseStart_7799135 : Nat := 118140960795 + 7799135 * 2 ^ 59
def prefixEnd_7799135 : Nat := 4983230072969 + 3 ^ 40 * 7799135 * 2
def baseEnd_7799135 : Nat := 4004704944303448582144937

theorem tailTrace_7799135 : CollatzResearch.WordTrace tailWord_7799135 prefixEnd_7799135 4004704944303448582144937 := by
  unfold tailWord_7799135
  simp only [CollatzResearch.WordTrace]
  refine ⟨284457822600073356058270859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189638548400048904038847239 284457822600073356058270859)
  ·
    refine ⟨426686733900110034087406289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284457822600073356058270859 426686733900110034087406289)
    ·
      refine ⟨320015050425082525565554717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426686733900110034087406289 320015050425082525565554717)
      ·
        refine ⟨120005643909405947087083019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320015050425082525565554717 120005643909405947087083019)
        ·
          refine ⟨180008465864108920630624529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120005643909405947087083019 180008465864108920630624529)
          ·
            refine ⟨135006349398081690472968397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180008465864108920630624529 135006349398081690472968397)
            ·
              refine ⟨50627381024280633927363149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135006349398081690472968397 50627381024280633927363149)
              ·
                refine ⟨18985267884105237722761181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50627381024280633927363149 18985267884105237722761181)
                ·
                  refine ⟨7119475456539464146035443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18985267884105237722761181 7119475456539464146035443)
                  ·
                    refine ⟨10679213184809196219053165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7119475456539464146035443 10679213184809196219053165)
                    ·
                      refine ⟨4004704944303448582144937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679213184809196219053165 4004704944303448582144937)
                      ·
                        rfl

theorem cell23_7799135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_7799135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799135 prefixEnd_7799135 := by exact prefixLift 7799135
  have htrace : WordTrace (prefixWord ++ tailWord_7799135) baseStart_7799135 baseEnd_7799135 := by
    simpa [prefixWord, tailWord_7799135, baseEnd_7799135] using wordTrace_append hprefix tailTrace_7799135
  have hstable : (prefixWord ++ tailWord_7799135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799135).length < 2 ^ (prefixWord ++ tailWord_7799135).sum := by decide
  have hdescent : baseEnd_7799135 < baseStart_7799135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799175 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_7799175 : Nat := 118140960795 + 7799175 * 2 ^ 59
def prefixEnd_7799175 : Nat := 4983230072969 + 3 ^ 40 * 7799175 * 2
def baseEnd_7799175 : Nat := 4004725483529628425644753

theorem tailTrace_7799175 : CollatzResearch.WordTrace tailWord_7799175 prefixEnd_7799175 4004725483529628425644753 := by
  unfold tailWord_7799175
  simp only [CollatzResearch.WordTrace]
  refine ⟨284459281519928442889726979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189639521013285628593151319 284459281519928442889726979)
  ·
    refine ⟨426688922279892664334590469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284459281519928442889726979 426688922279892664334590469)
    ·
      refine ⟨80004172927479874562735713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426688922279892664334590469 80004172927479874562735713)
      ·
        refine ⟨60003129695609905922051785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80004172927479874562735713 60003129695609905922051785)
        ·
          refine ⟨45002347271707429441538839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60003129695609905922051785 45002347271707429441538839)
          ·
            refine ⟨67503520907561144162308259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45002347271707429441538839 67503520907561144162308259)
            ·
              refine ⟨101255281361341716243462389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67503520907561144162308259 101255281361341716243462389)
              ·
                refine ⟨9492682627625785897824599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101255281361341716243462389 9492682627625785897824599)
                ·
                  refine ⟨14239023941438678846736899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9492682627625785897824599 14239023941438678846736899)
                  ·
                    refine ⟨21358535912158018270105349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14239023941438678846736899 21358535912158018270105349)
                    ·
                      refine ⟨4004725483529628425644753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21358535912158018270105349 4004725483529628425644753)
                      ·
                        rfl

theorem cell23_7799175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_7799175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799175 prefixEnd_7799175 := by exact prefixLift 7799175
  have htrace : WordTrace (prefixWord ++ tailWord_7799175) baseStart_7799175 baseEnd_7799175 := by
    simpa [prefixWord, tailWord_7799175, baseEnd_7799175] using wordTrace_append hprefix tailTrace_7799175
  have hstable : (prefixWord ++ tailWord_7799175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799175).length < 2 ^ (prefixWord ++ tailWord_7799175).sum := by decide
  have hdescent : baseEnd_7799175 < baseStart_7799175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799202 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_7799202 : Nat := 118140960795 + 7799202 * 2 ^ 59
def prefixEnd_7799202 : Nat := 4983230072969 + 3 ^ 40 * 7799202 * 2
def baseEnd_7799202 : Nat := 1334913115835766606669043

theorem tailTrace_7799202 : CollatzResearch.WordTrace tailWord_7799202 prefixEnd_7799202 1334913115835766606669043 := by
  unfold tailWord_7799202
  simp only [CollatzResearch.WordTrace]
  refine ⟨71115066572707656625239965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189640177527220417667306573 71115066572707656625239965)
  ·
    refine ⟨26668149964765371234464987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71115066572707656625239965 26668149964765371234464987)
    ·
      refine ⟨40002224947148056851697481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26668149964765371234464987 40002224947148056851697481)
      ·
        refine ⟨30001668710361042638773111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40002224947148056851697481 30001668710361042638773111)
        ·
          refine ⟨45002503065541563958159667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30001668710361042638773111 45002503065541563958159667)
          ·
            refine ⟨67503754598312345937239501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45002503065541563958159667 67503754598312345937239501)
            ·
              refine ⟨25313907974367129726464813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67503754598312345937239501 25313907974367129726464813)
              ·
                refine ⟨9492715490387673647424305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25313907974367129726464813 9492715490387673647424305)
                ·
                  refine ⟨7119536617790755235568229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9492715490387673647424305 7119536617790755235568229)
                  ·
                    refine ⟨1334913115835766606669043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119536617790755235568229 1334913115835766606669043)
                    ·
                      rfl

theorem cell23_7799202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_7799202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799202 prefixEnd_7799202 := by exact prefixLift 7799202
  have htrace : WordTrace (prefixWord ++ tailWord_7799202) baseStart_7799202 baseEnd_7799202 := by
    simpa [prefixWord, tailWord_7799202, baseEnd_7799202] using wordTrace_append hprefix tailTrace_7799202
  have hstable : (prefixWord ++ tailWord_7799202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799202).length < 2 ^ (prefixWord ++ tailWord_7799202).sum := by decide
  have hdescent : baseEnd_7799202 < baseStart_7799202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799225 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 3]
def baseStart_7799225 : Nat := 118140960795 + 7799225 * 2 ^ 59
def prefixEnd_7799225 : Nat := 4983230072969 + 3 ^ 40 * 7799225 * 2
def baseEnd_7799225 : Nat := 4004751157562353230019523

theorem tailTrace_7799225 : CollatzResearch.WordTrace tailWord_7799225 prefixEnd_7799225 4004751157562353230019523 := by
  unfold tailWord_7799225
  simp only [CollatzResearch.WordTrace]
  refine ⟨284461105169747301429047129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189640736779831534286031419 284461105169747301429047129)
  ·
    refine ⟨213345828877310476071785347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284461105169747301429047129 213345828877310476071785347)
    ·
      refine ⟨320018743315965714107678021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213345828877310476071785347 320018743315965714107678021)
      ·
        refine ⟨60003514371743571395189629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320018743315965714107678021 60003514371743571395189629)
        ·
          refine ⟨22501317889403839273196111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60003514371743571395189629 22501317889403839273196111)
          ·
            refine ⟨33751976834105758909794167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22501317889403839273196111 33751976834105758909794167)
            ·
              refine ⟨50627965251158638364691251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33751976834105758909794167 50627965251158638364691251)
              ·
                refine ⟨75941947876737957547036877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50627965251158638364691251 75941947876737957547036877)
                ·
                  refine ⟨28478230453776734080138829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75941947876737957547036877 28478230453776734080138829)
                  ·
                    refine ⟨10679336420166275280052061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28478230453776734080138829 10679336420166275280052061)
                    ·
                      refine ⟨4004751157562353230019523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679336420166275280052061 4004751157562353230019523)
                      ·
                        rfl

theorem cell23_7799225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_7799225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799225 prefixEnd_7799225 := by exact prefixLift 7799225
  have htrace : WordTrace (prefixWord ++ tailWord_7799225) baseStart_7799225 baseEnd_7799225 := by
    simpa [prefixWord, tailWord_7799225, baseEnd_7799225] using wordTrace_append hprefix tailTrace_7799225
  have hstable : (prefixWord ++ tailWord_7799225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799225).length < 2 ^ (prefixWord ++ tailWord_7799225).sum := by decide
  have hdescent : baseEnd_7799225 < baseStart_7799225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799229 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_7799229 : Nat := 118140960795 + 7799229 * 2 ^ 59
def prefixEnd_7799229 : Nat := 4983230072969 + 3 ^ 40 * 7799229 * 2
def baseEnd_7799229 : Nat := 4004753211484971214369505

theorem tailTrace_7799229 : CollatzResearch.WordTrace tailWord_7799229 prefixEnd_7799229 4004753211484971214369505 := by
  unfold tailWord_7799229
  simp only [CollatzResearch.WordTrace]
  refine ⟨284461251061732810112192741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189640834041155206741461827 284461251061732810112192741)
  ·
    refine ⟨53336484574074901896036139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284461251061732810112192741 53336484574074901896036139)
    ·
      refine ⟨80004726861112352844054209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53336484574074901896036139 80004726861112352844054209)
      ·
        refine ⟨60003545145834264633040657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80004726861112352844054209 60003545145834264633040657)
        ·
          refine ⟨45002658859375698474780493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60003545145834264633040657 45002658859375698474780493)
          ·
            refine ⟨16875997072265886928042685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45002658859375698474780493 16875997072265886928042685)
            ·
              refine ⟨6328498902099707598016007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16875997072265886928042685 6328498902099707598016007)
              ·
                refine ⟨9492748353149561397024011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6328498902099707598016007 9492748353149561397024011)
                ·
                  refine ⟨14239122529724342095536017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9492748353149561397024011 14239122529724342095536017)
                  ·
                    refine ⟨10679341897293256571652013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14239122529724342095536017 10679341897293256571652013)
                    ·
                      refine ⟨4004753211484971214369505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679341897293256571652013 4004753211484971214369505)
                      ·
                        rfl

theorem cell23_7799229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_7799229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799229 prefixEnd_7799229 := by exact prefixLift 7799229
  have htrace : WordTrace (prefixWord ++ tailWord_7799229) baseStart_7799229 baseEnd_7799229 := by
    simpa [prefixWord, tailWord_7799229, baseEnd_7799229] using wordTrace_append hprefix tailTrace_7799229
  have hstable : (prefixWord ++ tailWord_7799229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799229).length < 2 ^ (prefixWord ++ tailWord_7799229).sum := by decide
  have hdescent : baseEnd_7799229 < baseStart_7799229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799288 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 9]
def baseStart_7799288 : Nat := 118140960795 + 7799288 * 2 ^ 59
def prefixEnd_7799288 : Nat := 4983230072969 + 3 ^ 40 * 7799288 * 2
def baseEnd_7799288 : Nat := 444975945204842942614637

theorem tailTrace_7799288 : CollatzResearch.WordTrace tailWord_7799288 prefixEnd_7799288 444975945204842942614637 := by
  unfold tailWord_7799288
  simp only [CollatzResearch.WordTrace]
  refine ⟨142231701484259531594295259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189642268645679375459060345 142231701484259531594295259)
  ·
    refine ⟨213347552226389297391442889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142231701484259531594295259 213347552226389297391442889)
    ·
      refine ⟨160010664169791973043582167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213347552226389297391442889 160010664169791973043582167)
      ·
        refine ⟨240015996254687959565373251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160010664169791973043582167 240015996254687959565373251)
        ·
          refine ⟨360023994382031939348059877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240015996254687959565373251 360023994382031939348059877)
          ·
            refine ⟨67504498946630988627761227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360023994382031939348059877 67504498946630988627761227)
            ·
              refine ⟨101256748419946482941641841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67504498946630988627761227 101256748419946482941641841)
              ·
                refine ⟨75942561314959862206231381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101256748419946482941641841 75942561314959862206231381)
                ·
                  refine ⟨444975945204842942614637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75942561314959862206231381 444975945204842942614637)
                  ·
                    rfl

theorem cell23_7799288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 9].length) (baseStart_7799288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799288 prefixEnd_7799288 := by exact prefixLift 7799288
  have htrace : WordTrace (prefixWord ++ tailWord_7799288) baseStart_7799288 baseEnd_7799288 := by
    simpa [prefixWord, tailWord_7799288, baseEnd_7799288] using wordTrace_append hprefix tailTrace_7799288
  have hstable : (prefixWord ++ tailWord_7799288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799288).length < 2 ^ (prefixWord ++ tailWord_7799288).sum := by decide
  have hdescent : baseEnd_7799288 < baseStart_7799288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799309 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7799309 : Nat := 118140960795 + 7799309 * 2 ^ 59
def prefixEnd_7799309 : Nat := 4983230072969 + 3 ^ 40 * 7799309 * 2
def baseEnd_7799309 : Nat := 1334931429979110300456379

theorem tailTrace_7799309 : CollatzResearch.WordTrace tailWord_7799309 prefixEnd_7799309 1334931429979110300456379 := by
  unfold tailWord_7799309
  simp only [CollatzResearch.WordTrace]
  refine ⟨284464168901442983775104981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189642779267628655850069987 284464168901442983775104981)
  ·
    refine ⟨6667128958627569932229023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 284464168901442983775104981 6667128958627569932229023)
    ·
      refine ⟨10000693437941354898343535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6667128958627569932229023 10000693437941354898343535)
      ·
        refine ⟨15001040156912032347515303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000693437941354898343535 15001040156912032347515303)
        ·
          refine ⟨22501560235368048521272955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15001040156912032347515303 22501560235368048521272955)
          ·
            refine ⟨33752340353052072781909433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22501560235368048521272955 33752340353052072781909433)
            ·
              refine ⟨25314255264789054586432075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33752340353052072781909433 25314255264789054586432075)
              ·
                refine ⟨37971382897183581879648113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25314255264789054586432075 37971382897183581879648113)
                ·
                  refine ⟨28478537172887686409736085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37971382897183581879648113 28478537172887686409736085)
                  ·
                    refine ⟨1334931429979110300456379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28478537172887686409736085 1334931429979110300456379)
                    ·
                      rfl

theorem cell23_7799309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7799309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799309 prefixEnd_7799309 := by exact prefixLift 7799309
  have htrace : WordTrace (prefixWord ++ tailWord_7799309) baseStart_7799309 baseEnd_7799309 := by
    simpa [prefixWord, tailWord_7799309, baseEnd_7799309] using wordTrace_append hprefix tailTrace_7799309
  have hstable : (prefixWord ++ tailWord_7799309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799309).length < 2 ^ (prefixWord ++ tailWord_7799309).sum := by decide
  have hdescent : baseEnd_7799309 < baseStart_7799309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799315 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 3]
def baseStart_7799315 : Nat := 118140960795 + 7799315 * 2 ^ 59
def prefixEnd_7799315 : Nat := 4983230072969 + 3 ^ 40 * 7799315 * 2
def baseEnd_7799315 : Nat := 4004797370821257877894109

theorem tailTrace_7799315 : CollatzResearch.WordTrace tailWord_7799315 prefixEnd_7799315 4004797370821257877894109 := by
  unfold tailWord_7799315
  simp only [CollatzResearch.WordTrace]
  refine ⟨284464387739421246799823399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189642925159614164533215599 284464387739421246799823399)
  ·
    refine ⟨426696581609131870199735099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284464387739421246799823399 426696581609131870199735099)
    ·
      refine ⟨640044872413697805299602649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426696581609131870199735099 640044872413697805299602649)
      ·
        refine ⟨480033654310273353974701987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640044872413697805299602649 480033654310273353974701987)
        ·
          refine ⟨720050481465410030962052981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480033654310273353974701987 720050481465410030962052981)
          ·
            refine ⟨67504732637382190402692467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 720050481465410030962052981 67504732637382190402692467)
            ·
              refine ⟨101257098956073285604038701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67504732637382190402692467 101257098956073285604038701)
              ·
                refine ⟨37971412108527482101514513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101257098956073285604038701 37971412108527482101514513)
                ·
                  refine ⟨28478559081395611576135885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37971412108527482101514513 28478559081395611576135885)
                  ·
                    refine ⟨10679459655523354341050957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28478559081395611576135885 10679459655523354341050957)
                    ·
                      refine ⟨4004797370821257877894109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679459655523354341050957 4004797370821257877894109)
                      ·
                        rfl

theorem cell23_7799315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_7799315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799315 prefixEnd_7799315 := by exact prefixLift 7799315
  have htrace : WordTrace (prefixWord ++ tailWord_7799315) baseStart_7799315 baseEnd_7799315 := by
    simpa [prefixWord, tailWord_7799315, baseEnd_7799315] using wordTrace_append hprefix tailTrace_7799315
  have hstable : (prefixWord ++ tailWord_7799315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799315).length < 2 ^ (prefixWord ++ tailWord_7799315).sum := by decide
  have hdescent : baseEnd_7799315 < baseStart_7799315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799316 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_7799316 : Nat := 118140960795 + 7799316 * 2 ^ 59
def prefixEnd_7799316 : Nat := 4983230072969 + 3 ^ 40 * 7799316 * 2
def baseEnd_7799316 : Nat := 4004797884301912373981605

theorem tailTrace_7799316 : CollatzResearch.WordTrace tailWord_7799316 prefixEnd_7799316 4004797884301912373981605 := by
  unfold tailWord_7799316
  simp only [CollatzResearch.WordTrace]
  refine ⟨142232212106208811985304901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189642949474945082647073201 142232212106208811985304901)
  ·
    refine ⟨26668539769914152247244669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142232212106208811985304901 26668539769914152247244669)
    ·
      refine ⟨10000702413717807092716751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26668539769914152247244669 10000702413717807092716751)
      ·
        refine ⟨15001053620576710639075127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000702413717807092716751 15001053620576710639075127)
        ·
          refine ⟨22501580430865065958612691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15001053620576710639075127 22501580430865065958612691)
          ·
            refine ⟨33752370646297598937919037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22501580430865065958612691 33752370646297598937919037)
            ·
              refine ⟨12657138992361599601719639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33752370646297598937919037 12657138992361599601719639)
              ·
                refine ⟨18985708488542399402579459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12657138992361599601719639 18985708488542399402579459)
                ·
                  refine ⟨28478562732813599103869189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18985708488542399402579459 28478562732813599103869189)
                  ·
                    refine ⟨5339730512402549831975473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28478562732813599103869189 5339730512402549831975473)
                    ·
                      refine ⟨4004797884301912373981605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339730512402549831975473 4004797884301912373981605)
                      ·
                        rfl

theorem cell23_7799316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_7799316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799316 prefixEnd_7799316 := by exact prefixLift 7799316
  have htrace : WordTrace (prefixWord ++ tailWord_7799316) baseStart_7799316 baseEnd_7799316 := by
    simpa [prefixWord, tailWord_7799316, baseEnd_7799316] using wordTrace_append hprefix tailTrace_7799316
  have hstable : (prefixWord ++ tailWord_7799316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799316).length < 2 ^ (prefixWord ++ tailWord_7799316).sum := by decide
  have hdescent : baseEnd_7799316 < baseStart_7799316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799372 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 1, 6, 2]
def baseStart_7799372 : Nat := 118140960795 + 7799372 * 2 ^ 59
def prefixEnd_7799372 : Nat := 4983230072969 + 3 ^ 40 * 7799372 * 2
def baseEnd_7799372 : Nat := 4004826639218564154881347

theorem tailTrace_7799372 : CollatzResearch.WordTrace tailWord_7799372 prefixEnd_7799372 4004826639218564154881347 := by
  unfold tailWord_7799372
  simp only [CollatzResearch.WordTrace]
  refine ⟨142233233350107372767324185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189644311133476497023098913 142233233350107372767324185)
  ·
    refine ⟨106674925012580529575493139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142233233350107372767324185 106674925012580529575493139)
    ·
      refine ⟨160012387518870794363239709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106674925012580529575493139 160012387518870794363239709)
      ·
        refine ⟨60004645319576547886214891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160012387518870794363239709 60004645319576547886214891)
        ·
          refine ⟨90006967979364821829322337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60004645319576547886214891 90006967979364821829322337)
          ·
            refine ⟨67505225984523616371991753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90006967979364821829322337 67505225984523616371991753)
            ·
              refine ⟨50628919488392712278993815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67505225984523616371991753 50628919488392712278993815)
              ·
                refine ⟨75943379232589068418490723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50628919488392712278993815 75943379232589068418490723)
                ·
                  refine ⟨113915068848883602627736085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75943379232589068418490723 113915068848883602627736085)
                  ·
                    refine ⟨5339768852291418873175129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113915068848883602627736085 5339768852291418873175129)
                    ·
                      refine ⟨4004826639218564154881347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339768852291418873175129 4004826639218564154881347)
                      ·
                        rfl

theorem cell23_7799372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_7799372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799372 prefixEnd_7799372 := by exact prefixLift 7799372
  have htrace : WordTrace (prefixWord ++ tailWord_7799372) baseStart_7799372 baseEnd_7799372 := by
    simpa [prefixWord, tailWord_7799372, baseEnd_7799372] using wordTrace_append hprefix tailTrace_7799372
  have hstable : (prefixWord ++ tailWord_7799372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799372).length < 2 ^ (prefixWord ++ tailWord_7799372).sum := by decide
  have hdescent : baseEnd_7799372 < baseStart_7799372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799375 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 3]
def baseStart_7799375 : Nat := 118140960795 + 7799375 * 2 ^ 59
def prefixEnd_7799375 : Nat := 4983230072969 + 3 ^ 40 * 7799375 * 2
def baseEnd_7799375 : Nat := 4004828179660527643143833

theorem tailTrace_7799375 : CollatzResearch.WordTrace tailWord_7799375 prefixEnd_7799375 4004828179660527643143833 := by
  unfold tailWord_7799375
  simp only [CollatzResearch.WordTrace]
  refine ⟨284466576119203877047007579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189644384079469251364671719 284466576119203877047007579)
  ·
    refine ⟨426699864178805815570511369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284466576119203877047007579 426699864178805815570511369)
    ·
      refine ⟨320024898134104361677883527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426699864178805815570511369 320024898134104361677883527)
      ·
        refine ⟨480037347201156542516825291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320024898134104361677883527 480037347201156542516825291)
        ·
          refine ⟨720056020801734813775237937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480037347201156542516825291 720056020801734813775237937)
          ·
            refine ⟨540042015601301110331428453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720056020801734813775237937 540042015601301110331428453)
            ·
              refine ⟨101257877925243958187142835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540042015601301110331428453 101257877925243958187142835)
              ·
                refine ⟨151886816887865937280714253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101257877925243958187142835 151886816887865937280714253)
                ·
                  refine ⟨56957556332949726480267845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151886816887865937280714253 56957556332949726480267845)
                  ·
                    refine ⟨10679541812428073715050221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56957556332949726480267845 10679541812428073715050221)
                    ·
                      refine ⟨4004828179660527643143833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679541812428073715050221 4004828179660527643143833)
                      ·
                        rfl

theorem cell23_7799375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_7799375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799375 prefixEnd_7799375 := by exact prefixLift 7799375
  have htrace : WordTrace (prefixWord ++ tailWord_7799375) baseStart_7799375 baseEnd_7799375 := by
    simpa [prefixWord, tailWord_7799375, baseEnd_7799375] using wordTrace_append hprefix tailTrace_7799375
  have hstable : (prefixWord ++ tailWord_7799375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799375).length < 2 ^ (prefixWord ++ tailWord_7799375).sum := by decide
  have hdescent : baseEnd_7799375 < baseStart_7799375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799392 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3]
def baseStart_7799392 : Nat := 118140960795 + 7799392 * 2 ^ 59
def prefixEnd_7799392 : Nat := 4983230072969 + 3 ^ 40 * 7799392 * 2
def baseEnd_7799392 : Nat := 4004836908831654076631255

theorem tailTrace_7799392 : CollatzResearch.WordTrace tailWord_7799392 prefixEnd_7799392 4004836908831654076631255 := by
  unfold tailWord_7799392
  simp only [CollatzResearch.WordTrace]
  refine ⟨142233598080071144475188215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189644797440094859300250953 142233598080071144475188215)
  ·
    refine ⟨213350397120106716712782323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142233598080071144475188215 213350397120106716712782323)
    ·
      refine ⟨320025595680160075069173485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213350397120106716712782323 320025595680160075069173485)
      ·
        refine ⟨120009598380060028150940057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320025595680160075069173485 120009598380060028150940057)
        ·
          refine ⟨90007198785045021113205043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120009598380060028150940057 90007198785045021113205043)
          ·
            refine ⟨135010798177567531669807565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90007198785045021113205043 135010798177567531669807565)
            ·
              refine ⟨50629049316587824376177837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135010798177567531669807565 50629049316587824376177837)
              ·
                refine ⟨18985893493720434141066689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50629049316587824376177837 18985893493720434141066689)
                ·
                  refine ⟨14239420120290325605800017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18985893493720434141066689 14239420120290325605800017)
                  ·
                    refine ⟨10679565090217744204350013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14239420120290325605800017 10679565090217744204350013)
                    ·
                      refine ⟨4004836908831654076631255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679565090217744204350013 4004836908831654076631255)
                      ·
                        rfl

theorem cell23_7799392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_7799392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799392 prefixEnd_7799392 := by exact prefixLift 7799392
  have htrace : WordTrace (prefixWord ++ tailWord_7799392) baseStart_7799392 baseEnd_7799392 := by
    simpa [prefixWord, tailWord_7799392, baseEnd_7799392] using wordTrace_append hprefix tailTrace_7799392
  have hstable : (prefixWord ++ tailWord_7799392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799392).length < 2 ^ (prefixWord ++ tailWord_7799392).sum := by decide
  have hdescent : baseEnd_7799392 < baseStart_7799392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799399 : List Nat := [1, 1, 5, 1, 1, 1, 1, 7, 1, 4]
def baseStart_7799399 : Nat := 118140960795 + 7799399 * 2 ^ 59
def prefixEnd_7799399 : Nat := 4983230072969 + 3 ^ 40 * 7799399 * 2
def baseEnd_7799399 : Nat := 1334946834398745183081241

theorem tailTrace_7799399 : CollatzResearch.WordTrace tailWord_7799399 prefixEnd_7799399 1334946834398745183081241 := by
  unfold tailWord_7799399
  simp only [CollatzResearch.WordTrace]
  refine ⟨284467451471116929145881251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189644967647411286097254167 284467451471116929145881251)
  ·
    refine ⟨426701177206675393718821877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284467451471116929145881251 426701177206675393718821877)
    ·
      refine ⟨40003235363125818161139551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426701177206675393718821877 40003235363125818161139551)
      ·
        refine ⟨60004853044688727241709327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40003235363125818161139551 60004853044688727241709327)
        ·
          refine ⟨90007279567033090862563991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60004853044688727241709327 90007279567033090862563991)
          ·
            refine ⟨135010919350549636293845987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90007279567033090862563991 135010919350549636293845987)
            ·
              refine ⟨202516379025824454440768981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135010919350549636293845987 202516379025824454440768981)
              ·
                refine ⟨4746477633417760650955523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 202516379025824454440768981 4746477633417760650955523)
                ·
                  refine ⟨7119716450126640976433285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746477633417760650955523 7119716450126640976433285)
                  ·
                    refine ⟨1334946834398745183081241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119716450126640976433285 1334946834398745183081241)
                    ·
                      rfl

theorem cell23_7799399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_7799399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799399 prefixEnd_7799399 := by exact prefixLift 7799399
  have htrace : WordTrace (prefixWord ++ tailWord_7799399) baseStart_7799399 baseEnd_7799399 := by
    simpa [prefixWord, tailWord_7799399, baseEnd_7799399] using wordTrace_append hprefix tailTrace_7799399
  have hstable : (prefixWord ++ tailWord_7799399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799399).length < 2 ^ (prefixWord ++ tailWord_7799399).sum := by decide
  have hdescent : baseEnd_7799399 < baseStart_7799399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799463 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 6]
def baseStart_7799463 : Nat := 118140960795 + 7799463 * 2 ^ 59
def prefixEnd_7799463 : Nat := 4983230072969 + 3 ^ 40 * 7799463 * 2
def baseEnd_7799463 : Nat := 444985929550902588760381

theorem tailTrace_7799463 : CollatzResearch.WordTrace tailWord_7799463 prefixEnd_7799463 444985929550902588760381 := by
  unfold tailWord_7799463
  simp only [CollatzResearch.WordTrace]
  refine ⟨284469785742885068076211043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189646523828590045384140695 284469785742885068076211043)
  ·
    refine ⟨426704678614327602114316565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284469785742885068076211043 426704678614327602114316565)
    ·
      refine ⟨20001781810046606349108589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 426704678614327602114316565 20001781810046606349108589)
      ·
        refine ⟨7500668178767477380915721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20001781810046606349108589 7500668178767477380915721)
        ·
          refine ⟨5625501134075608035686791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7500668178767477380915721 5625501134075608035686791)
          ·
            refine ⟨8438251701113412053530187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625501134075608035686791 8438251701113412053530187)
            ·
              refine ⟨12657377551670118080295281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438251701113412053530187 12657377551670118080295281)
              ·
                refine ⟨9493033163752588560221461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12657377551670118080295281 9493033163752588560221461)
                ·
                  refine ⟨444985929550902588760381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9493033163752588560221461 444985929550902588760381)
                  ·
                    rfl

theorem cell23_7799463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 6].length) (baseStart_7799463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799463 prefixEnd_7799463 := by exact prefixLift 7799463
  have htrace : WordTrace (prefixWord ++ tailWord_7799463) baseStart_7799463 baseEnd_7799463 := by
    simpa [prefixWord, tailWord_7799463, baseEnd_7799463] using wordTrace_append hprefix tailTrace_7799463
  have hstable : (prefixWord ++ tailWord_7799463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799463).length < 2 ^ (prefixWord ++ tailWord_7799463).sum := by decide
  have hdescent : baseEnd_7799463 < baseStart_7799463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799473 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7799473 : Nat := 118140960795 + 7799473 * 2 ^ 59
def prefixEnd_7799473 : Nat := 4983230072969 + 3 ^ 40 * 7799473 * 2
def baseEnd_7799473 : Nat := 4004878500764668259718383

theorem tailTrace_7799473 : CollatzResearch.WordTrace tailWord_7799473 prefixEnd_7799473 4004878500764668259718383 := by
  unfold tailWord_7799473
  simp only [CollatzResearch.WordTrace]
  refine ⟨284470150472848839784075073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189646766981899226522716715 284470150472848839784075073)
  ·
    refine ⟨213352612854636629838056305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284470150472848839784075073 213352612854636629838056305)
    ·
      refine ⟨160014459640977472378542229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213352612854636629838056305 160014459640977472378542229)
      ·
        refine ⟨7500677795670819017744167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160014459640977472378542229 7500677795670819017744167)
        ·
          refine ⟨11251016693506228526616251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500677795670819017744167 11251016693506228526616251)
          ·
            refine ⟨16876525040259342789924377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11251016693506228526616251 16876525040259342789924377)
            ·
              refine ⟨12657393780194507092443283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16876525040259342789924377 12657393780194507092443283)
              ·
                refine ⟨18986090670291760638664925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12657393780194507092443283 18986090670291760638664925)
                ·
                  refine ⟨7119784001359410239499347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18986090670291760638664925 7119784001359410239499347)
                  ·
                    refine ⟨10679676002039115359249021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7119784001359410239499347 10679676002039115359249021)
                    ·
                      refine ⟨4004878500764668259718383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679676002039115359249021 4004878500764668259718383)
                      ·
                        rfl

theorem cell23_7799473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7799473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799473 prefixEnd_7799473 := by exact prefixLift 7799473
  have htrace : WordTrace (prefixWord ++ tailWord_7799473) baseStart_7799473 baseEnd_7799473 := by
    simpa [prefixWord, tailWord_7799473, baseEnd_7799473] using wordTrace_append hprefix tailTrace_7799473
  have hstable : (prefixWord ++ tailWord_7799473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799473).length < 2 ^ (prefixWord ++ tailWord_7799473).sum := by decide
  have hdescent : baseEnd_7799473 < baseStart_7799473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799482 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_7799482 : Nat := 118140960795 + 7799482 * 2 ^ 59
def prefixEnd_7799482 : Nat := 4983230072969 + 3 ^ 40 * 7799482 * 2
def baseEnd_7799482 : Nat := 4004883122090558724505841

theorem tailTrace_7799482 : CollatzResearch.WordTrace tailWord_7799482 prefixEnd_7799482 4004883122090558724505841 := by
  unfold tailWord_7799482
  simp only [CollatzResearch.WordTrace]
  refine ⟨71117619682454058580288175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189646985819877489547435133 71117619682454058580288175)
  ·
    refine ⟨106676429523681087870432263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71117619682454058580288175 106676429523681087870432263)
    ·
      refine ⟨160014644285521631805648395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106676429523681087870432263 160014644285521631805648395)
      ·
        refine ⟨240021966428282447708472593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160014644285521631805648395 240021966428282447708472593)
        ·
          refine ⟨180016474821211835781354445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240021966428282447708472593 180016474821211835781354445)
          ·
            refine ⟨67506178057954438418007917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180016474821211835781354445 67506178057954438418007917)
            ·
              refine ⟨25314816771732914406752969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67506178057954438418007917 25314816771732914406752969)
              ·
                refine ⟨18986112578799685805064727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25314816771732914406752969 18986112578799685805064727)
                ·
                  refine ⟨28479168868199528707597091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18986112578799685805064727 28479168868199528707597091)
                  ·
                    refine ⟨42718753302299293061395637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28479168868199528707597091 42718753302299293061395637)
                    ·
                      refine ⟨4004883122090558724505841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42718753302299293061395637 4004883122090558724505841)
                      ·
                        rfl

theorem cell23_7799482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_7799482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799482 prefixEnd_7799482 := by exact prefixLift 7799482
  have htrace : WordTrace (prefixWord ++ tailWord_7799482) baseStart_7799482 baseEnd_7799482 := by
    simpa [prefixWord, tailWord_7799482, baseEnd_7799482] using wordTrace_append hprefix tailTrace_7799482
  have hstable : (prefixWord ++ tailWord_7799482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799482).length < 2 ^ (prefixWord ++ tailWord_7799482).sum := by decide
  have hdescent : baseEnd_7799482 < baseStart_7799482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799496 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_7799496 : Nat := 118140960795 + 7799496 * 2 ^ 59
def prefixEnd_7799496 : Nat := 4983230072969 + 3 ^ 40 * 7799496 * 2
def baseEnd_7799496 : Nat := 4004890310819721669730777

theorem tailTrace_7799496 : CollatzResearch.WordTrace tailWord_7799496 prefixEnd_7799496 4004890310819721669730777 := by
  unfold tailWord_7799496
  simp only [CollatzResearch.WordTrace]
  refine ⟨142235494675882757356081171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189647326234510343141441561 142235494675882757356081171)
  ·
    refine ⟨213353242013824136034121757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142235494675882757356081171 213353242013824136034121757)
    ·
      refine ⟨80007465755184051012795659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213353242013824136034121757 80007465755184051012795659)
      ·
        refine ⟨120011198632776076519193489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80007465755184051012795659 120011198632776076519193489)
        ·
          refine ⟨90008398974582057389395117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120011198632776076519193489 90008398974582057389395117)
          ·
            refine ⟨33753149615468271521023169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90008398974582057389395117 33753149615468271521023169)
            ·
              refine ⟨25314862211601203640767377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33753149615468271521023169 25314862211601203640767377)
              ·
                refine ⟨18986146658700902730575533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25314862211601203640767377 18986146658700902730575533)
                ·
                  refine ⟨7119804997012838523965825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18986146658700902730575533 7119804997012838523965825)
                  ·
                    refine ⟨5339853747759628892974369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7119804997012838523965825 5339853747759628892974369)
                    ·
                      refine ⟨4004890310819721669730777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339853747759628892974369 4004890310819721669730777)
                      ·
                        rfl

theorem cell23_7799496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_7799496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799496 prefixEnd_7799496 := by exact prefixLift 7799496
  have htrace : WordTrace (prefixWord ++ tailWord_7799496) baseStart_7799496 baseEnd_7799496 := by
    simpa [prefixWord, tailWord_7799496, baseEnd_7799496] using wordTrace_append hprefix tailTrace_7799496
  have hstable : (prefixWord ++ tailWord_7799496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799496).length < 2 ^ (prefixWord ++ tailWord_7799496).sum := by decide
  have hdescent : baseEnd_7799496 < baseStart_7799496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799502 : List Nat := [4, 1, 1, 1, 3, 3, 1, 9]
def baseStart_7799502 : Nat := 118140960795 + 7799502 * 2 ^ 59
def prefixEnd_7799502 : Nat := 4983230072969 + 3 ^ 40 * 7799502 * 2
def baseEnd_7799502 : Nat := 148329384877912912824287

theorem tailTrace_7799502 : CollatzResearch.WordTrace tailWord_7799502 prefixEnd_7799502 148329384877912912824287 := by
  unfold tailWord_7799502
  simp only [CollatzResearch.WordTrace]
  refine ⟨35558901023717972217110095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189647472126495851824587173 35558901023717972217110095)
  ·
    refine ⟨53338351535576958325665143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35558901023717972217110095 53338351535576958325665143)
    ·
      refine ⟨80007527303365437488497715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53338351535576958325665143 80007527303365437488497715)
      ·
        refine ⟨120011290955048156232746573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80007527303365437488497715 120011290955048156232746573)
        ·
          refine ⟨45004234108143058587279965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120011290955048156232746573 45004234108143058587279965)
          ·
            refine ⟨16876587790553646970229987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45004234108143058587279965 16876587790553646970229987)
            ·
              refine ⟨25314881685830470455344981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16876587790553646970229987 25314881685830470455344981)
              ·
                refine ⟨148329384877912912824287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25314881685830470455344981 148329384877912912824287)
                ·
                  rfl

theorem cell23_7799502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_7799502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799502 prefixEnd_7799502 := by exact prefixLift 7799502
  have htrace : WordTrace (prefixWord ++ tailWord_7799502) baseStart_7799502 baseEnd_7799502 := by
    simpa [prefixWord, tailWord_7799502, baseEnd_7799502] using wordTrace_append hprefix tailTrace_7799502
  have hstable : (prefixWord ++ tailWord_7799502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799502).length < 2 ^ (prefixWord ++ tailWord_7799502).sum := by decide
  have hdescent : baseEnd_7799502 < baseStart_7799502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799515 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 6, 7]
def baseStart_7799515 : Nat := 118140960795 + 7799515 * 2 ^ 59
def prefixEnd_7799515 : Nat := 4983230072969 + 3 ^ 40 * 7799515 * 2
def baseEnd_7799515 : Nat := 1334966688984052365131063

theorem tailTrace_7799515 : CollatzResearch.WordTrace tailWord_7799515 prefixEnd_7799515 1334966688984052365131063 := by
  unfold tailWord_7799515
  simp only [CollatzResearch.WordTrace]
  refine ⟨284471682338696680957103999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189647788225797787304735999 284471682338696680957103999)
  ·
    refine ⟨426707523508045021435655999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284471682338696680957103999 426707523508045021435655999)
    ·
      refine ⟨640061285262067532153483999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426707523508045021435655999 640061285262067532153483999)
      ·
        refine ⟨960091927893101298230225999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640061285262067532153483999 960091927893101298230225999)
        ·
          refine ⟨1440137891839651947345338999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960091927893101298230225999 1440137891839651947345338999)
          ·
            refine ⟨2160206837759477921018008499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440137891839651947345338999 2160206837759477921018008499)
            ·
              refine ⟨3240310256639216881527012749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160206837759477921018008499 3240310256639216881527012749)
              ·
                refine ⟨1215116346239706330572629781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3240310256639216881527012749 1215116346239706330572629781)
                ·
                  refine ⟨56958578729986234245592021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1215116346239706330572629781 56958578729986234245592021)
                  ·
                    refine ⟨1334966688984052365131063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56958578729986234245592021 1334966688984052365131063)
                    ·
                      rfl

theorem cell23_7799515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_7799515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799515 prefixEnd_7799515 := by exact prefixLift 7799515
  have htrace : WordTrace (prefixWord ++ tailWord_7799515) baseStart_7799515 baseEnd_7799515 := by
    simpa [prefixWord, tailWord_7799515, baseEnd_7799515] using wordTrace_append hprefix tailTrace_7799515
  have hstable : (prefixWord ++ tailWord_7799515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799515).length < 2 ^ (prefixWord ++ tailWord_7799515).sum := by decide
  have hdescent : baseEnd_7799515 < baseStart_7799515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799516 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7799516 : Nat := 118140960795 + 7799516 * 2 ^ 59
def prefixEnd_7799516 : Nat := 4983230072969 + 3 ^ 40 * 7799516 * 2
def baseEnd_7799516 : Nat := 4004900580432811591480685

theorem tailTrace_7799516 : CollatzResearch.WordTrace tailWord_7799516 prefixEnd_7799516 4004900580432811591480685 := by
  unfold tailWord_7799516
  simp only [CollatzResearch.WordTrace]
  refine ⟨142235859405846529063945201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189647812541128705418593601 142235859405846529063945201)
  ·
    refine ⟨106676894554384896797958901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142235859405846529063945201 106676894554384896797958901)
    ·
      refine ⟨10000958864473584074808647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106676894554384896797958901 10000958864473584074808647)
      ·
        refine ⟨15001438296710376112212971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000958864473584074808647 15001438296710376112212971)
        ·
          refine ⟨22502157445065564168319457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15001438296710376112212971 22502157445065564168319457)
          ·
            refine ⟨16876618083799173126239593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22502157445065564168319457 16876618083799173126239593)
            ·
              refine ⟨12657463562849379844679695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16876618083799173126239593 12657463562849379844679695)
              ·
                refine ⟨18986195344274069767019543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12657463562849379844679695 18986195344274069767019543)
                ·
                  refine ⟨28479293016411104650529315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18986195344274069767019543 28479293016411104650529315)
                  ·
                    refine ⟨42718939524616656975793973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28479293016411104650529315 42718939524616656975793973)
                    ·
                      refine ⟨4004900580432811591480685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42718939524616656975793973 4004900580432811591480685)
                      ·
                        rfl

theorem cell23_7799516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7799516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799516 prefixEnd_7799516 := by exact prefixLift 7799516
  have htrace : WordTrace (prefixWord ++ tailWord_7799516) baseStart_7799516 baseEnd_7799516 := by
    simpa [prefixWord, tailWord_7799516, baseEnd_7799516] using wordTrace_append hprefix tailTrace_7799516
  have hstable : (prefixWord ++ tailWord_7799516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799516).length < 2 ^ (prefixWord ++ tailWord_7799516).sum := by decide
  have hdescent : baseEnd_7799516 < baseStart_7799516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799529 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 3]
def baseStart_7799529 : Nat := 118140960795 + 7799529 * 2 ^ 59
def prefixEnd_7799529 : Nat := 4983230072969 + 3 ^ 40 * 7799529 * 2
def baseEnd_7799529 : Nat := 4004907255681320040618125

theorem tailTrace_7799529 : CollatzResearch.WordTrace tailWord_7799529 prefixEnd_7799529 4004907255681320040618125 := by
  unfold tailWord_7799529
  simp only [CollatzResearch.WordTrace]
  refine ⟨284472192960645961348113641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189648128640430640898742427 284472192960645961348113641)
  ·
    refine ⟨213354144720484471011085231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284472192960645961348113641 213354144720484471011085231)
    ·
      refine ⟨320031217080726706516627847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213354144720484471011085231 320031217080726706516627847)
      ·
        refine ⟨480046825621090059774941771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320031217080726706516627847 480046825621090059774941771)
        ·
          refine ⟨720070238431635089662412657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480046825621090059774941771 720070238431635089662412657)
          ·
            refine ⟨540052678823726317246809493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720070238431635089662412657 540052678823726317246809493)
            ·
              refine ⟨25314969319862171120944195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 540052678823726317246809493 25314969319862171120944195)
              ·
                refine ⟨37972453979793256681416293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25314969319862171120944195 37972453979793256681416293)
                ·
                  refine ⟨7119835121211235627765555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37972453979793256681416293 7119835121211235627765555)
                  ·
                    refine ⟨10679752681816853441648333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7119835121211235627765555 10679752681816853441648333)
                    ·
                      refine ⟨4004907255681320040618125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679752681816853441648333 4004907255681320040618125)
                      ·
                        rfl

theorem cell23_7799529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 1, 3].length) (baseStart_7799529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799529 prefixEnd_7799529 := by exact prefixLift 7799529
  have htrace : WordTrace (prefixWord ++ tailWord_7799529) baseStart_7799529 baseEnd_7799529 := by
    simpa [prefixWord, tailWord_7799529, baseEnd_7799529] using wordTrace_append hprefix tailTrace_7799529
  have hstable : (prefixWord ++ tailWord_7799529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799529).length < 2 ^ (prefixWord ++ tailWord_7799529).sum := by decide
  have hdescent : baseEnd_7799529 < baseStart_7799529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799539 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 3, 3, 2]
def baseStart_7799539 : Nat := 118140960795 + 7799539 * 2 ^ 59
def prefixEnd_7799539 : Nat := 4983230072969 + 3 ^ 40 * 7799539 * 2
def baseEnd_7799539 : Nat := 4004912390487865001493079

theorem tailTrace_7799539 : CollatzResearch.WordTrace tailWord_7799539 prefixEnd_7799539 4004912390487865001493079 := by
  unfold tailWord_7799539
  simp only [CollatzResearch.WordTrace]
  refine ⟨284472557690609733055977671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189648371793739822037318447 284472557690609733055977671)
  ·
    refine ⟨426708836535914599583966507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284472557690609733055977671 426708836535914599583966507)
    ·
      refine ⟨640063254803871899375949761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426708836535914599583966507 640063254803871899375949761)
      ·
        refine ⟨480047441102903924531962321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640063254803871899375949761 480047441102903924531962321)
        ·
          refine ⟨360035580827177943398971741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480047441102903924531962321 360035580827177943398971741)
          ·
            refine ⟨135013342810191728774614403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360035580827177943398971741 135013342810191728774614403)
            ·
              refine ⟨202520014215287593161921605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135013342810191728774614403 202520014215287593161921605)
              ·
                refine ⟨37972502665366423717860301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202520014215287593161921605 37972502665366423717860301)
                ·
                  refine ⟨14239688499512408894197613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37972502665366423717860301 14239688499512408894197613)
                  ·
                    refine ⟨5339883187317153335324105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14239688499512408894197613 5339883187317153335324105)
                    ·
                      refine ⟨4004912390487865001493079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339883187317153335324105 4004912390487865001493079)
                      ·
                        rfl

theorem cell23_7799539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3, 2].length) (baseStart_7799539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799539 prefixEnd_7799539 := by exact prefixLift 7799539
  have htrace : WordTrace (prefixWord ++ tailWord_7799539) baseStart_7799539 baseEnd_7799539 := by
    simpa [prefixWord, tailWord_7799539, baseEnd_7799539] using wordTrace_append hprefix tailTrace_7799539
  have hstable : (prefixWord ++ tailWord_7799539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799539).length < 2 ^ (prefixWord ++ tailWord_7799539).sum := by decide
  have hdescent : baseEnd_7799539 < baseStart_7799539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799540 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7799540 : Nat := 118140960795 + 7799540 * 2 ^ 59
def prefixEnd_7799540 : Nat := 4983230072969 + 3 ^ 40 * 7799540 * 2
def baseEnd_7799540 : Nat := 1334970967989506499193525

theorem tailTrace_7799540 : CollatzResearch.WordTrace tailWord_7799540 prefixEnd_7799540 1334970967989506499193525 := by
  unfold tailWord_7799540
  simp only [CollatzResearch.WordTrace]
  refine ⟨142236297081803055113382037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189648396109070740151176049 142236297081803055113382037)
  ·
    refine ⟨6667326425709518208439783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142236297081803055113382037 6667326425709518208439783)
    ·
      refine ⟨10000989638564277312659675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6667326425709518208439783 10000989638564277312659675)
      ·
        refine ⟨15001484457846415968989513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000989638564277312659675 15001484457846415968989513)
        ·
          refine ⟨11251113343384811976742135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15001484457846415968989513 11251113343384811976742135)
          ·
            refine ⟨16876670015077217965113203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11251113343384811976742135 16876670015077217965113203)
            ·
              refine ⟨25315005022615826947669805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16876670015077217965113203 25315005022615826947669805)
              ·
                refine ⟨9493126883480935105376177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25315005022615826947669805 9493126883480935105376177)
                ·
                  refine ⟨7119845162610701329032133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9493126883480935105376177 7119845162610701329032133)
                  ·
                    refine ⟨1334970967989506499193525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7119845162610701329032133 1334970967989506499193525)
                    ·
                      rfl

theorem cell23_7799540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7799540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799540 prefixEnd_7799540 := by exact prefixLift 7799540
  have htrace : WordTrace (prefixWord ++ tailWord_7799540) baseStart_7799540 baseEnd_7799540 := by
    simpa [prefixWord, tailWord_7799540, baseEnd_7799540] using wordTrace_append hprefix tailTrace_7799540
  have hstable : (prefixWord ++ tailWord_7799540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799540).length < 2 ^ (prefixWord ++ tailWord_7799540).sum := by decide
  have hdescent : baseEnd_7799540 < baseStart_7799540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799556 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7799556 : Nat := 118140960795 + 7799556 * 2 ^ 59
def prefixEnd_7799556 : Nat := 4983230072969 + 3 ^ 40 * 7799556 * 2
def baseEnd_7799556 : Nat := 4004921119658991434980501

theorem tailTrace_7799556 : CollatzResearch.WordTrace tailWord_7799556 prefixEnd_7799556 4004921119658991434980501 := by
  unfold tailWord_7799556
  simp only [CollatzResearch.WordTrace]
  refine ⟨142236588865774072479673261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189648785154365429972897681 142236588865774072479673261)
  ·
    refine ⟨53338720824665277179877473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142236588865774072479673261 53338720824665277179877473)
    ·
      refine ⟨40004040618498957884908105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53338720824665277179877473 40004040618498957884908105)
      ·
        refine ⟨30003030463874218413681079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40004040618498957884908105 30003030463874218413681079)
        ·
          refine ⟨45004545695811327620521619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30003030463874218413681079 45004545695811327620521619)
          ·
            refine ⟨67506818543716991430782429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45004545695811327620521619 67506818543716991430782429)
            ·
              refine ⟨25315056953893871786543411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67506818543716991430782429 25315056953893871786543411)
              ·
                refine ⟨37972585430840807679815117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25315056953893871786543411 37972585430840807679815117)
                ·
                  refine ⟨14239719536565302879930669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37972585430840807679815117 14239719536565302879930669)
                  ·
                    refine ⟨5339894826211988579974001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14239719536565302879930669 5339894826211988579974001)
                    ·
                      refine ⟨4004921119658991434980501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339894826211988579974001 4004921119658991434980501)
                      ·
                        rfl

theorem cell23_7799556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7799556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799556 prefixEnd_7799556 := by exact prefixLift 7799556
  have htrace : WordTrace (prefixWord ++ tailWord_7799556) baseStart_7799556 baseEnd_7799556 := by
    simpa [prefixWord, tailWord_7799556, baseEnd_7799556] using wordTrace_append hprefix tailTrace_7799556
  have hstable : (prefixWord ++ tailWord_7799556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799556).length < 2 ^ (prefixWord ++ tailWord_7799556).sum := by decide
  have hdescent : baseEnd_7799556 < baseStart_7799556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799569 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 3, 4, 2]
def baseStart_7799569 : Nat := 118140960795 + 7799569 * 2 ^ 59
def prefixEnd_7799569 : Nat := 4983230072969 + 3 ^ 40 * 7799569 * 2
def baseEnd_7799569 : Nat := 4004927794907499884117941

theorem tailTrace_7799569 : CollatzResearch.WordTrace tailWord_7799569 prefixEnd_7799569 4004927794907499884117941 := by
  unfold tailWord_7799569
  simp only [CollatzResearch.WordTrace]
  refine ⟨284473651880501048179569761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189649101253667365453046507 284473651880501048179569761)
  ·
    refine ⟨213355238910375786134677321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284473651880501048179569761 213355238910375786134677321)
    ·
      refine ⟨160016429182781839601007991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213355238910375786134677321 160016429182781839601007991)
      ·
        refine ⟨240024643774172759401511987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160016429182781839601007991 240024643774172759401511987)
        ·
          refine ⟨360036965661259139102267981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240024643774172759401511987 360036965661259139102267981)
          ·
            refine ⟨135013862122972177163350493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360036965661259139102267981 135013862122972177163350493)
            ·
              refine ⟨50630198296114566436256435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135013862122972177163350493 50630198296114566436256435)
              ·
                refine ⟨75945297444171849654384653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50630198296114566436256435 75945297444171849654384653)
                ·
                  refine ⟨28479486541564443620394245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75945297444171849654384653 28479486541564443620394245)
                  ·
                    refine ⟨5339903726543333178823921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28479486541564443620394245 5339903726543333178823921)
                    ·
                      refine ⟨4004927794907499884117941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339903726543333178823921 4004927794907499884117941)
                      ·
                        rfl

theorem cell23_7799569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_7799569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799569 prefixEnd_7799569 := by exact prefixLift 7799569
  have htrace : WordTrace (prefixWord ++ tailWord_7799569) baseStart_7799569 baseEnd_7799569 := by
    simpa [prefixWord, tailWord_7799569, baseEnd_7799569] using wordTrace_append hprefix tailTrace_7799569
  have hstable : (prefixWord ++ tailWord_7799569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799569).length < 2 ^ (prefixWord ++ tailWord_7799569).sum := by decide
  have hdescent : baseEnd_7799569 < baseStart_7799569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799573 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_7799573 : Nat := 118140960795 + 7799573 * 2 ^ 59
def prefixEnd_7799573 : Nat := 4983230072969 + 3 ^ 40 * 7799573 * 2
def baseEnd_7799573 : Nat := 4004929848830117868467923

theorem tailTrace_7799573 : CollatzResearch.WordTrace tailWord_7799573 prefixEnd_7799573 4004929848830117868467923 := by
  unfold tailWord_7799573
  simp only [CollatzResearch.WordTrace]
  refine ⟨284473797772486556862715373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189649198514991037908476915 284473797772486556862715373)
  ·
    refine ⟨106677674164682458823518265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284473797772486556862715373 106677674164682458823518265)
    ·
      refine ⟨80008255623511844117638699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106677674164682458823518265 80008255623511844117638699)
      ·
        refine ⟨120012383435267766176458049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80008255623511844117638699 120012383435267766176458049)
        ·
          refine ⟨90009287576450824632343537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120012383435267766176458049 90009287576450824632343537)
          ·
            refine ⟨67506965682338118474257653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90009287576450824632343537 67506965682338118474257653)
            ·
              refine ⟨6328778032719198606961655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67506965682338118474257653 6328778032719198606961655)
              ·
                refine ⟨9493167049078797910442483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6328778032719198606961655 9493167049078797910442483)
                ·
                  refine ⟨14239750573618196865663725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493167049078797910442483 14239750573618196865663725)
                  ·
                    refine ⟨5339906465106823824623897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14239750573618196865663725 5339906465106823824623897)
                    ·
                      refine ⟨4004929848830117868467923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339906465106823824623897 4004929848830117868467923)
                      ·
                        rfl

theorem cell23_7799573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_7799573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799573 prefixEnd_7799573 := by exact prefixLift 7799573
  have htrace : WordTrace (prefixWord ++ tailWord_7799573) baseStart_7799573 baseEnd_7799573 := by
    simpa [prefixWord, tailWord_7799573, baseEnd_7799573] using wordTrace_append hprefix tailTrace_7799573
  have hstable : (prefixWord ++ tailWord_7799573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799573).length < 2 ^ (prefixWord ++ tailWord_7799573).sum := by decide
  have hdescent : baseEnd_7799573 < baseStart_7799573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799581 : List Nat := [1, 4, 2, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7799581 : Nat := 118140960795 + 7799581 * 2 ^ 59
def prefixEnd_7799581 : Nat := 4983230072969 + 3 ^ 40 * 7799581 * 2
def baseEnd_7799581 : Nat := 4004933956675353837167887

theorem tailTrace_7799581 : CollatzResearch.WordTrace tailWord_7799581 prefixEnd_7799581 4004933956675353837167887 := by
  unfold tailWord_7799581
  simp only [CollatzResearch.WordTrace]
  refine ⟨284474089556457574229006597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189649393037638382819337731 284474089556457574229006597)
  ·
    refine ⟨53338891791835795167938737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284474089556457574229006597 53338891791835795167938737)
    ·
      refine ⟨40004168843876846375954053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53338891791835795167938737 40004168843876846375954053)
      ·
        refine ⟨7500781658226908695491385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40004168843876846375954053 7500781658226908695491385)
        ·
          refine ⟨5625586243670181521618539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7500781658226908695491385 5625586243670181521618539)
          ·
            refine ⟨8438379365505272282427809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625586243670181521618539 8438379365505272282427809)
            ·
              refine ⟨6328784524128954211820857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8438379365505272282427809 6328784524128954211820857)
              ·
                refine ⟨4746588393096715658865643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6328784524128954211820857 4746588393096715658865643)
                ·
                  refine ⟨7119882589645073488298465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746588393096715658865643 7119882589645073488298465)
                  ·
                    refine ⟨5339911942233805116223849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7119882589645073488298465 5339911942233805116223849)
                    ·
                      refine ⟨4004933956675353837167887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339911942233805116223849 4004933956675353837167887)
                      ·
                        rfl

theorem cell23_7799581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7799581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799581 prefixEnd_7799581 := by exact prefixLift 7799581
  have htrace : WordTrace (prefixWord ++ tailWord_7799581) baseStart_7799581 baseEnd_7799581 := by
    simpa [prefixWord, tailWord_7799581, baseEnd_7799581] using wordTrace_append hprefix tailTrace_7799581
  have hstable : (prefixWord ++ tailWord_7799581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799581).length < 2 ^ (prefixWord ++ tailWord_7799581).sum := by decide
  have hdescent : baseEnd_7799581 < baseStart_7799581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799603 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 2, 2, 2]
def baseStart_7799603 : Nat := 118140960795 + 7799603 * 2 ^ 59
def prefixEnd_7799603 : Nat := 4983230072969 + 3 ^ 40 * 7799603 * 2
def baseEnd_7799603 : Nat := 4004945253249752751092785

theorem tailTrace_7799603 : CollatzResearch.WordTrace tailWord_7799603 prefixEnd_7799603 4004945253249752751092785 := by
  unfold tailWord_7799603
  simp only [CollatzResearch.WordTrace]
  refine ⟨284474891962377871986307463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189649927974918581324204975 284474891962377871986307463)
  ·
    refine ⟨426712337943566807979461195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284474891962377871986307463 426712337943566807979461195)
    ·
      refine ⟨640068506915350211969191793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426712337943566807979461195 640068506915350211969191793)
      ·
        refine ⟨480051380186512658976893845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640068506915350211969191793 480051380186512658976893845)
        ·
          refine ⟨22502408446242780889541899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 480051380186512658976893845 22502408446242780889541899)
          ·
            refine ⟨33753612669364171334312849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22502408446242780889541899 33753612669364171334312849)
            ·
              refine ⟨25315209502023128500734637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33753612669364171334312849 25315209502023128500734637)
              ·
                refine ⟨9493203563258673187775489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25315209502023128500734637 9493203563258673187775489)
                ·
                  refine ⟨7119902672444004890831617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9493203563258673187775489 7119902672444004890831617)
                  ·
                    refine ⟨5339927004333003668123713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7119902672444004890831617 5339927004333003668123713)
                    ·
                      refine ⟨4004945253249752751092785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5339927004333003668123713 4004945253249752751092785)
                      ·
                        rfl

theorem cell23_7799603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 2, 2].length) (baseStart_7799603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799603 prefixEnd_7799603 := by exact prefixLift 7799603
  have htrace : WordTrace (prefixWord ++ tailWord_7799603) baseStart_7799603 baseEnd_7799603 := by
    simpa [prefixWord, tailWord_7799603, baseEnd_7799603] using wordTrace_append hprefix tailTrace_7799603
  have hstable : (prefixWord ++ tailWord_7799603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799603).length < 2 ^ (prefixWord ++ tailWord_7799603).sum := by decide
  have hdescent : baseEnd_7799603 < baseStart_7799603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799632 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_7799632 : Nat := 118140960795 + 7799632 * 2 ^ 59
def prefixEnd_7799632 : Nat := 4983230072969 + 3 ^ 40 * 7799632 * 2
def baseEnd_7799632 : Nat := 4004960144188733137630151

theorem tailTrace_7799632 : CollatzResearch.WordTrace tailWord_7799632 prefixEnd_7799632 4004960144188733137630151 := by
  unfold tailWord_7799632
  simp only [CollatzResearch.WordTrace]
  refine ⟨142237974839636404969556575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189650633119515206626075433 142237974839636404969556575)
  ·
    refine ⟨213356962259454607454334863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142237974839636404969556575 213356962259454607454334863)
    ·
      refine ⟨320035443389181911181502295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213356962259454607454334863 320035443389181911181502295)
      ·
        refine ⟨480053165083772866772253443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320035443389181911181502295 480053165083772866772253443)
        ·
          refine ⟨720079747625659300158380165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480053165083772866772253443 720079747625659300158380165)
          ·
            refine ⟨135014952679811118779696281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 720079747625659300158380165 135014952679811118779696281)
            ·
              refine ⟨101261214509858339084772211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135014952679811118779696281 101261214509858339084772211)
              ·
                refine ⟨151891821764787508627158317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101261214509858339084772211 151891821764787508627158317)
                ·
                  refine ⟨56959433161795315735184369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151891821764787508627158317 56959433161795315735184369)
                  ·
                    refine ⟨42719574871346486801388277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56959433161795315735184369 42719574871346486801388277)
                    ·
                      refine ⟨4004960144188733137630151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42719574871346486801388277 4004960144188733137630151)
                      ·
                        rfl

theorem cell23_7799632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_7799632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799632 prefixEnd_7799632 := by exact prefixLift 7799632
  have htrace : WordTrace (prefixWord ++ tailWord_7799632) baseStart_7799632 baseEnd_7799632 := by
    simpa [prefixWord, tailWord_7799632, baseEnd_7799632] using wordTrace_append hprefix tailTrace_7799632
  have hstable : (prefixWord ++ tailWord_7799632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799632).length < 2 ^ (prefixWord ++ tailWord_7799632).sum := by decide
  have hdescent : baseEnd_7799632 < baseStart_7799632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799672 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_7799672 : Nat := 118140960795 + 7799672 * 2 ^ 59
def prefixEnd_7799672 : Nat := 4983230072969 + 3 ^ 40 * 7799672 * 2
def baseEnd_7799672 : Nat := 4004980683414912981129967

theorem tailTrace_7799672 : CollatzResearch.WordTrace tailWord_7799672 prefixEnd_7799672 4004980683414912981129967 := by
  unfold tailWord_7799672
  simp only [CollatzResearch.WordTrace]
  refine ⟨142238704299563948385284635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189651605732751931180379513 142238704299563948385284635)
  ·
    refine ⟨213358056449345922577926953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142238704299563948385284635 213358056449345922577926953)
    ·
      refine ⟨160018542337009441933445215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213358056449345922577926953 160018542337009441933445215)
      ·
        refine ⟨240027813505514162900167823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160018542337009441933445215 240027813505514162900167823)
        ·
          refine ⟨360041720258271244350251735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240027813505514162900167823 360041720258271244350251735)
          ·
            refine ⟨540062580387406866525377603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360041720258271244350251735 540062580387406866525377603)
            ·
              refine ⟨810093870581110299788066405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540062580387406866525377603 810093870581110299788066405)
              ·
                refine ⟨151892600733958181210262451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810093870581110299788066405 151892600733958181210262451)
                ·
                  refine ⟨227838901100937271815393677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151892600733958181210262451 227838901100937271815393677)
                  ·
                    refine ⟨85439587912851476930772629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227838901100937271815393677 85439587912851476930772629)
                    ·
                      refine ⟨4004980683414912981129967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85439587912851476930772629 4004980683414912981129967)
                      ·
                        rfl

theorem cell23_7799672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_7799672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799672 prefixEnd_7799672 := by exact prefixLift 7799672
  have htrace : WordTrace (prefixWord ++ tailWord_7799672) baseStart_7799672 baseEnd_7799672 := by
    simpa [prefixWord, tailWord_7799672, baseEnd_7799672] using wordTrace_append hprefix tailTrace_7799672
  have hstable : (prefixWord ++ tailWord_7799672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799672).length < 2 ^ (prefixWord ++ tailWord_7799672).sum := by decide
  have hdescent : baseEnd_7799672 < baseStart_7799672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799679 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 3]
def baseStart_7799679 : Nat := 118140960795 + 7799679 * 2 ^ 59
def prefixEnd_7799679 : Nat := 4983230072969 + 3 ^ 40 * 7799679 * 2
def baseEnd_7799679 : Nat := 4004984277779494453742435

theorem tailTrace_7799679 : CollatzResearch.WordTrace tailWord_7799679 prefixEnd_7799679 4004984277779494453742435 := by
  unfold tailWord_7799679
  simp only [CollatzResearch.WordTrace]
  refine ⟨284477663910102536966074091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189651775940068357977382727 284477663910102536966074091)
  ·
    refine ⟨426716495865153805449111137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284477663910102536966074091 426716495865153805449111137)
    ·
      refine ⟨320037371898865354086833353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426716495865153805449111137 320037371898865354086833353)
      ·
        refine ⟨240028028924149015565125015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320037371898865354086833353 240028028924149015565125015)
        ·
          refine ⟨360042043386223523347687523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240028028924149015565125015 360042043386223523347687523)
          ·
            refine ⟨540063065079335285021531285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360042043386223523347687523 540063065079335285021531285)
            ·
              refine ⟨25315456175593841485384279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 540063065079335285021531285 25315456175593841485384279)
              ·
                refine ⟨37973184263390762228076419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25315456175593841485384279 37973184263390762228076419)
                ·
                  refine ⟨56959776395086143342114629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37973184263390762228076419 56959776395086143342114629)
                  ·
                    refine ⟨10679958074078651876646493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56959776395086143342114629 10679958074078651876646493)
                    ·
                      refine ⟨4004984277779494453742435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10679958074078651876646493 4004984277779494453742435)
                      ·
                        rfl

theorem cell23_7799679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_7799679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799679 prefixEnd_7799679 := by exact prefixLift 7799679
  have htrace : WordTrace (prefixWord ++ tailWord_7799679) baseStart_7799679 baseEnd_7799679 := by
    simpa [prefixWord, tailWord_7799679, baseEnd_7799679] using wordTrace_append hprefix tailTrace_7799679
  have hstable : (prefixWord ++ tailWord_7799679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799679).length < 2 ^ (prefixWord ++ tailWord_7799679).sum := by decide
  have hdescent : baseEnd_7799679 < baseStart_7799679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799794 : List Nat := [3, 2, 1, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7799794 : Nat := 118140960795 + 7799794 * 2 ^ 59
def prefixEnd_7799794 : Nat := 4983230072969 + 3 ^ 40 * 7799794 * 2
def baseEnd_7799794 : Nat := 4005043328054761503804407

theorem tailTrace_7799794 : CollatzResearch.WordTrace tailWord_7799794 prefixEnd_7799794 4005043328054761503804407 := by
  unfold tailWord_7799794
  simp only [CollatzResearch.WordTrace]
  refine ⟨71120464576171477901627609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189654572203123941071006957 71120464576171477901627609)
  ·
    refine ⟨53340348432128608426220707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71120464576171477901627609 53340348432128608426220707)
    ·
      refine ⟨80010522648192912639331061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53340348432128608426220707 80010522648192912639331061)
      ·
        refine ⟨7500986498268085559937287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80010522648192912639331061 7500986498268085559937287)
        ·
          refine ⟨11251479747402128339905931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500986498268085559937287 11251479747402128339905931)
          ·
            refine ⟨16877219621103192509858897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11251479747402128339905931 16877219621103192509858897)
            ·
              refine ⟨12657914715827394382394173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16877219621103192509858897 12657914715827394382394173)
              ·
                refine ⟨4746718018435272893397815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12657914715827394382394173 4746718018435272893397815)
                ·
                  refine ⟨7120077027652909340096723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746718018435272893397815 7120077027652909340096723)
                  ·
                    refine ⟨10680115541479364010145085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7120077027652909340096723 10680115541479364010145085)
                    ·
                      refine ⟨4005043328054761503804407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680115541479364010145085 4005043328054761503804407)
                      ·
                        rfl

theorem cell23_7799794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7799794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799794 prefixEnd_7799794 := by exact prefixLift 7799794
  have htrace : WordTrace (prefixWord ++ tailWord_7799794) baseStart_7799794 baseEnd_7799794 := by
    simpa [prefixWord, tailWord_7799794, baseEnd_7799794] using wordTrace_append hprefix tailTrace_7799794
  have hstable : (prefixWord ++ tailWord_7799794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799794).length < 2 ^ (prefixWord ++ tailWord_7799794).sum := by decide
  have hdescent : baseEnd_7799794 < baseStart_7799794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799833 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 3]
def baseStart_7799833 : Nat := 118140960795 + 7799833 * 2 ^ 59
def prefixEnd_7799833 : Nat := 4983230072969 + 3 ^ 40 * 7799833 * 2
def baseEnd_7799833 : Nat := 4005063353800286851216727

theorem tailTrace_7799833 : CollatzResearch.WordTrace tailWord_7799833 prefixEnd_7799833 4005063353800286851216727 := by
  unfold tailWord_7799833
  simp only [CollatzResearch.WordTrace]
  refine ⟨284483280751544621267180153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189655520501029747511453435 284483280751544621267180153)
  ·
    refine ⟨213362460563658465950385115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284483280751544621267180153 213362460563658465950385115)
    ·
      refine ⟨320043690845487698925577673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213362460563658465950385115 320043690845487698925577673)
      ·
        refine ⟨240032768134115774194183255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320043690845487698925577673 240032768134115774194183255)
        ·
          refine ⟨360049152201173661291274883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240032768134115774194183255 360049152201173661291274883)
          ·
            refine ⟨540073728301760491936912325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360049152201173661291274883 540073728301760491936912325)
            ·
              refine ⟨101263824056580092238171061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540073728301760491936912325 101263824056580092238171061)
              ·
                refine ⟨9493483505304383647328537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101263824056580092238171061 9493483505304383647328537)
                ·
                  refine ⟨7120112628978287735496403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9493483505304383647328537 7120112628978287735496403)
                  ·
                    refine ⟨10680168943467431603244605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7120112628978287735496403 10680168943467431603244605)
                    ·
                      refine ⟨4005063353800286851216727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680168943467431603244605 4005063353800286851216727)
                      ·
                        rfl

theorem cell23_7799833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_7799833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799833 prefixEnd_7799833 := by exact prefixLift 7799833
  have htrace : WordTrace (prefixWord ++ tailWord_7799833) baseStart_7799833 baseEnd_7799833 := by
    simpa [prefixWord, tailWord_7799833, baseEnd_7799833] using wordTrace_append hprefix tailTrace_7799833
  have hstable : (prefixWord ++ tailWord_7799833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799833).length < 2 ^ (prefixWord ++ tailWord_7799833).sum := by decide
  have hdescent : baseEnd_7799833 < baseStart_7799833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799840 : List Nat := [2, 1, 1, 7, 1, 2, 2, 7]
def baseStart_7799840 : Nat := 118140960795 + 7799840 * 2 ^ 59
def prefixEnd_7799840 : Nat := 4983230072969 + 3 ^ 40 * 7799840 * 2
def baseEnd_7799840 : Nat := 148335812894995123104785

theorem tailTrace_7799840 : CollatzResearch.WordTrace tailWord_7799840 prefixEnd_7799840 148335812894995123104785 := by
  unfold tailWord_7799840
  simp only [CollatzResearch.WordTrace]
  refine ⟨142241768031259630731342487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189655690708346174308456649 142241768031259630731342487)
  ·
    refine ⟨213362652046889446097013731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142241768031259630731342487 213362652046889446097013731)
    ·
      refine ⟨320043978070334169145520597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213362652046889446097013731 320043978070334169145520597)
      ·
        refine ⟨7501030736023457089348139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 320043978070334169145520597 7501030736023457089348139)
        ·
          refine ⟨11251546104035185634022209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501030736023457089348139 11251546104035185634022209)
          ·
            refine ⟨8438659578026389225516657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11251546104035185634022209 8438659578026389225516657)
            ·
              refine ⟨6328994683519791919137493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8438659578026389225516657 6328994683519791919137493)
              ·
                refine ⟨148335812894995123104785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6328994683519791919137493 148335812894995123104785)
                ·
                  rfl

theorem cell23_7799840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 7].length) (baseStart_7799840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799840 prefixEnd_7799840 := by exact prefixLift 7799840
  have htrace : WordTrace (prefixWord ++ tailWord_7799840) baseStart_7799840 baseEnd_7799840 := by
    simpa [prefixWord, tailWord_7799840, baseEnd_7799840] using wordTrace_append hprefix tailTrace_7799840
  have hstable : (prefixWord ++ tailWord_7799840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799840).length < 2 ^ (prefixWord ++ tailWord_7799840).sum := by decide
  have hdescent : baseEnd_7799840 < baseStart_7799840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799886 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_7799886 : Nat := 118140960795 + 7799886 * 2 ^ 59
def prefixEnd_7799886 : Nat := 4983230072969 + 3 ^ 40 * 7799886 * 2
def baseEnd_7799886 : Nat := 4005090568274975143853983

theorem tailTrace_7799886 : CollatzResearch.WordTrace tailWord_7799886 prefixEnd_7799886 4005090568274975143853983 := by
  unfold tailWord_7799886
  simp only [CollatzResearch.WordTrace]
  refine ⟨35560651727544076414857439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189656809213568407545906341 35560651727544076414857439)
  ·
    refine ⟨53340977591316114622286159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35560651727544076414857439 53340977591316114622286159)
    ·
      refine ⟨80011466386974171933429239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53340977591316114622286159 80011466386974171933429239)
      ·
        refine ⟨120017199580461257900143859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80011466386974171933429239 120017199580461257900143859)
        ·
          refine ⟨180025799370691886850215789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120017199580461257900143859 180025799370691886850215789)
          ·
            refine ⟨67509674764009457568830921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180025799370691886850215789 67509674764009457568830921)
            ·
              refine ⟨50632256073007093176623191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67509674764009457568830921 50632256073007093176623191)
              ·
                refine ⟨75948384109510639764934787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50632256073007093176623191 75948384109510639764934787)
                ·
                  refine ⟨113922576164265959647402181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75948384109510639764934787 113922576164265959647402181)
                  ·
                    refine ⟨21360483030799867433887909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113922576164265959647402181 21360483030799867433887909)
                    ·
                      refine ⟨4005090568274975143853983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21360483030799867433887909 4005090568274975143853983)
                      ·
                        rfl

theorem cell23_7799886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_7799886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799886 prefixEnd_7799886 := by exact prefixLift 7799886
  have htrace : WordTrace (prefixWord ++ tailWord_7799886) baseStart_7799886 baseEnd_7799886 := by
    simpa [prefixWord, tailWord_7799886, baseEnd_7799886] using wordTrace_append hprefix tailTrace_7799886
  have hstable : (prefixWord ++ tailWord_7799886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799886).length < 2 ^ (prefixWord ++ tailWord_7799886).sum := by decide
  have hdescent : baseEnd_7799886 < baseStart_7799886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799894 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7799894 : Nat := 118140960795 + 7799894 * 2 ^ 59
def prefixEnd_7799894 : Nat := 4983230072969 + 3 ^ 40 * 7799894 * 2
def baseEnd_7799894 : Nat := 4005094676120211112553947

theorem tailTrace_7799894 : CollatzResearch.WordTrace tailWord_7799894 prefixEnd_7799894 4005094676120211112553947 := by
  unfold tailWord_7799894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17780344100270226792821921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189657003736215752456767157 17780344100270226792821921)
  ·
    refine ⟨13335258075202670094616441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17780344100270226792821921 13335258075202670094616441)
    ·
      refine ⟨10001443556402002570962331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13335258075202670094616441 10001443556402002570962331)
      ·
        refine ⟨15002165334603003856443497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10001443556402002570962331 15002165334603003856443497)
        ·
          refine ⟨11251624000952252892332623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15002165334603003856443497 11251624000952252892332623)
          ·
            refine ⟨16877436001428379338498935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11251624000952252892332623 16877436001428379338498935)
            ·
              refine ⟨25316154002142569007748403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16877436001428379338498935 25316154002142569007748403)
              ·
                refine ⟨37974231003213853511622605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25316154002142569007748403 37974231003213853511622605)
                ·
                  refine ⟨14240336626205195066858477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37974231003213853511622605 14240336626205195066858477)
                  ·
                    refine ⟨5340126234826948150071929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14240336626205195066858477 5340126234826948150071929)
                    ·
                      refine ⟨4005094676120211112553947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340126234826948150071929 4005094676120211112553947)
                      ·
                        rfl

theorem cell23_7799894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7799894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799894 prefixEnd_7799894 := by exact prefixLift 7799894
  have htrace : WordTrace (prefixWord ++ tailWord_7799894) baseStart_7799894 baseEnd_7799894 := by
    simpa [prefixWord, tailWord_7799894, baseEnd_7799894] using wordTrace_append hprefix tailTrace_7799894
  have hstable : (prefixWord ++ tailWord_7799894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799894).length < 2 ^ (prefixWord ++ tailWord_7799894).sum := by decide
  have hdescent : baseEnd_7799894 < baseStart_7799894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799933 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_7799933 : Nat := 118140960795 + 7799933 * 2 ^ 59
def prefixEnd_7799933 : Nat := 4983230072969 + 3 ^ 40 * 7799933 * 2
def baseEnd_7799933 : Nat := 4005114701865736459966267

theorem tailTrace_7799933 : CollatzResearch.WordTrace tailWord_7799933 prefixEnd_7799933 4005114701865736459966267 := by
  unfold tailWord_7799933
  simp only [CollatzResearch.WordTrace]
  refine ⟨284486928051182338345820453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189657952034121558897213635 284486928051182338345820453)
  ·
    refine ⟨53341299009596688439841335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284486928051182338345820453 53341299009596688439841335)
    ·
      refine ⟨80011948514395032659762003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53341299009596688439841335 80011948514395032659762003)
      ·
        refine ⟨120017922771592548989643005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80011948514395032659762003 120017922771592548989643005)
        ·
          refine ⟨45006721039347205871116127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120017922771592548989643005 45006721039347205871116127)
          ·
            refine ⟨67510081559020808806674191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45006721039347205871116127 67510081559020808806674191)
            ·
              refine ⟨101265122338531213210011287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67510081559020808806674191 101265122338531213210011287)
              ·
                refine ⟨151897683507796819815016931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101265122338531213210011287 151897683507796819815016931)
                ·
                  refine ⟨227846525261695229722525397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151897683507796819815016931 227846525261695229722525397)
                  ·
                    refine ⟨5340152935820981946621689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227846525261695229722525397 5340152935820981946621689)
                    ·
                      refine ⟨4005114701865736459966267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340152935820981946621689 4005114701865736459966267)
                      ·
                        rfl

theorem cell23_7799933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_7799933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799933 prefixEnd_7799933 := by exact prefixLift 7799933
  have htrace : WordTrace (prefixWord ++ tailWord_7799933) baseStart_7799933 baseEnd_7799933 := by
    simpa [prefixWord, tailWord_7799933, baseEnd_7799933] using wordTrace_append hprefix tailTrace_7799933
  have hstable : (prefixWord ++ tailWord_7799933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799933).length < 2 ^ (prefixWord ++ tailWord_7799933).sum := by decide
  have hdescent : baseEnd_7799933 < baseStart_7799933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799936 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_7799936 : Nat := 118140960795 + 7799936 * 2 ^ 59
def prefixEnd_7799936 : Nat := 4983230072969 + 3 ^ 40 * 7799936 * 2
def baseEnd_7799936 : Nat := 4005116242307699948228753

theorem tailTrace_7799936 : CollatzResearch.WordTrace tailWord_7799936 prefixEnd_7799936 4005116242307699948228753 := by
  unfold tailWord_7799936
  simp only [CollatzResearch.WordTrace]
  refine ⟨142243518735085734929089831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189658024980114313238786441 142243518735085734929089831)
  ·
    refine ⟨213365278102628602393634747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142243518735085734929089831 213365278102628602393634747)
    ·
      refine ⟨320047917153942903590452121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213365278102628602393634747 320047917153942903590452121)
      ·
        refine ⟨240035937865457177692839091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320047917153942903590452121 240035937865457177692839091)
        ·
          refine ⟨360053906798185766539258637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240035937865457177692839091 360053906798185766539258637)
          ·
            refine ⟨135020215049319662452221989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360053906798185766539258637 135020215049319662452221989)
            ·
              refine ⟨25316290321747436709791623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135020215049319662452221989 25316290321747436709791623)
              ·
                refine ⟨37974435482621155064687435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25316290321747436709791623 37974435482621155064687435)
                ·
                  refine ⟨56961653223931732597031153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37974435482621155064687435 56961653223931732597031153)
                  ·
                    refine ⟨42721239917948799447773365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56961653223931732597031153 42721239917948799447773365)
                    ·
                      refine ⟨4005116242307699948228753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42721239917948799447773365 4005116242307699948228753)
                      ·
                        rfl

theorem cell23_7799936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_7799936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799936 prefixEnd_7799936 := by exact prefixLift 7799936
  have htrace : WordTrace (prefixWord ++ tailWord_7799936) baseStart_7799936 baseEnd_7799936 := by
    simpa [prefixWord, tailWord_7799936, baseEnd_7799936] using wordTrace_append hprefix tailTrace_7799936
  have hstable : (prefixWord ++ tailWord_7799936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799936).length < 2 ^ (prefixWord ++ tailWord_7799936).sum := by decide
  have hdescent : baseEnd_7799936 < baseStart_7799936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799960 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 2, 5]
def baseStart_7799960 : Nat := 118140960795 + 7799960 * 2 ^ 59
def prefixEnd_7799960 : Nat := 4983230072969 + 3 ^ 40 * 7799960 * 2
def baseEnd_7799960 : Nat := 1335042855281135951442881

theorem tailTrace_7799960 : CollatzResearch.WordTrace tailWord_7799960 prefixEnd_7799960 1335042855281135951442881 := by
  unfold tailWord_7799960
  simp only [CollatzResearch.WordTrace]
  refine ⟨142243956411042260978526667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189658608548056347971368889 142243956411042260978526667)
  ·
    refine ⟨213365934616563391467790001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142243956411042260978526667 213365934616563391467790001)
    ·
      refine ⟨160024450962422543600842501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213365934616563391467790001 160024450962422543600842501)
      ·
        refine ⟨30004584555454226925157969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160024450962422543600842501 30004584555454226925157969)
        ·
          refine ⟨22503438416590670193868477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30004584555454226925157969 22503438416590670193868477)
          ·
            refine ⟨8438789406221501322700679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22503438416590670193868477 8438789406221501322700679)
            ·
              refine ⟨12658184109332251984051019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438789406221501322700679 12658184109332251984051019)
              ·
                refine ⟨18987276163998377976076529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12658184109332251984051019 18987276163998377976076529)
                ·
                  refine ⟨14240457122998783482057397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18987276163998377976076529 14240457122998783482057397)
                  ·
                    refine ⟨1335042855281135951442881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14240457122998783482057397 1335042855281135951442881)
                    ·
                      rfl

theorem cell23_7799960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_7799960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799960 prefixEnd_7799960 := by exact prefixLift 7799960
  have htrace : WordTrace (prefixWord ++ tailWord_7799960) baseStart_7799960 baseEnd_7799960 := by
    simpa [prefixWord, tailWord_7799960, baseEnd_7799960] using wordTrace_append hprefix tailTrace_7799960
  have hstable : (prefixWord ++ tailWord_7799960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799960).length < 2 ^ (prefixWord ++ tailWord_7799960).sum := by decide
  have hdescent : baseEnd_7799960 < baseStart_7799960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7799983 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 3]
def baseStart_7799983 : Nat := 118140960795 + 7799983 * 2 ^ 59
def prefixEnd_7799983 : Nat := 4983230072969 + 3 ^ 40 * 7799983 * 2
def baseEnd_7799983 : Nat := 4005140375898461264341037

theorem tailTrace_7799983 : CollatzResearch.WordTrace tailWord_7799983 prefixEnd_7799983 4005140375898461264341037 := by
  unfold tailWord_7799983
  simp only [CollatzResearch.WordTrace]
  refine ⟨284488751701001196885140603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189659167800667464590093735 284488751701001196885140603)
  ·
    refine ⟨426733127551501795327710905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284488751701001196885140603 426733127551501795327710905)
    ·
      refine ⟨320049845663626346495783179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426733127551501795327710905 320049845663626346495783179)
      ·
        refine ⟨480074768495439519743674769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320049845663626346495783179 480074768495439519743674769)
        ·
          refine ⟨360056076371579639807756077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480074768495439519743674769 360056076371579639807756077)
          ·
            refine ⟨135021028639342364927908529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360056076371579639807756077 135021028639342364927908529)
            ·
              refine ⟨101265771479506773695931397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135021028639342364927908529 101265771479506773695931397)
              ·
                refine ⟨18987332152407520067987137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101265771479506773695931397 18987332152407520067987137)
                ·
                  refine ⟨14240499114305640050990353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18987332152407520067987137 14240499114305640050990353)
                  ·
                    refine ⟨10680374335729230038242765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14240499114305640050990353 10680374335729230038242765)
                    ·
                      refine ⟨4005140375898461264341037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680374335729230038242765 4005140375898461264341037)
                      ·
                        rfl

theorem cell23_7799983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_7799983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7799983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7799983 prefixEnd_7799983 := by exact prefixLift 7799983
  have htrace : WordTrace (prefixWord ++ tailWord_7799983) baseStart_7799983 baseEnd_7799983 := by
    simpa [prefixWord, tailWord_7799983, baseEnd_7799983] using wordTrace_append hprefix tailTrace_7799983
  have hstable : (prefixWord ++ tailWord_7799983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7799983).length < 2 ^ (prefixWord ++ tailWord_7799983).sum := by decide
  have hdescent : baseEnd_7799983 < baseStart_7799983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7799983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800024 : List Nat := [2, 1, 2, 2, 5, 2, 1, 3, 1, 4]
def baseStart_7800024 : Nat := 118140960795 + 7800024 * 2 ^ 59
def prefixEnd_7800024 : Nat := 4983230072969 + 3 ^ 40 * 7800024 * 2
def baseEnd_7800024 : Nat := 1335053809535098534642783

theorem tailTrace_7800024 : CollatzResearch.WordTrace tailWord_7800024 prefixEnd_7800024 1335053809535098534642783 := by
  unfold tailWord_7800024
  simp only [CollatzResearch.WordTrace]
  refine ⟨142245123546926330443691563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189660164729235107258255417 142245123546926330443691563)
  ·
    refine ⟨213367685320389495665537345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142245123546926330443691563 213367685320389495665537345)
    ·
      refine ⟨160025763990292121749153009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213367685320389495665537345 160025763990292121749153009)
      ·
        refine ⟨120019322992719091311864757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160025763990292121749153009 120019322992719091311864757)
        ·
          refine ⟨11251811530567414810487321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120019322992719091311864757 11251811530567414810487321)
          ·
            refine ⟨8438858647925561107865491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11251811530567414810487321 8438858647925561107865491)
            ·
              refine ⟨12658287971888341661798237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438858647925561107865491 12658287971888341661798237)
              ·
                refine ⟨4746857989458128123174339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12658287971888341661798237 4746857989458128123174339)
                ·
                  refine ⟨7120286984187192184761509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746857989458128123174339 7120286984187192184761509)
                  ·
                    refine ⟨1335053809535098534642783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7120286984187192184761509 1335053809535098534642783)
                    ·
                      rfl

theorem cell23_7800024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_7800024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800024 prefixEnd_7800024 := by exact prefixLift 7800024
  have htrace : WordTrace (prefixWord ++ tailWord_7800024) baseStart_7800024 baseEnd_7800024 := by
    simpa [prefixWord, tailWord_7800024, baseEnd_7800024] using wordTrace_append hprefix tailTrace_7800024
  have hstable : (prefixWord ++ tailWord_7800024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800024).length < 2 ^ (prefixWord ++ tailWord_7800024).sum := by decide
  have hdescent : baseEnd_7800024 < baseStart_7800024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800087 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 1, 1, 4]
def baseStart_7800087 : Nat := 118140960795 + 7800087 * 2 ^ 59
def prefixEnd_7800087 : Nat := 4983230072969 + 3 ^ 40 * 7800087 * 2
def baseEnd_7800087 : Nat := 4005193777886528857440559

theorem tailTrace_7800087 : CollatzResearch.WordTrace tailWord_7800087 prefixEnd_7800087 4005193777886528857440559 := by
  unfold tailWord_7800087
  simp only [CollatzResearch.WordTrace]
  refine ⟨284492544892624422646926515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189661696595082948431284343 284492544892624422646926515)
  ·
    refine ⟨426738817338936633970389773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284492544892624422646926515 426738817338936633970389773)
    ·
      refine ⟨160027056502101237738896165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426738817338936633970389773 160027056502101237738896165)
      ·
        refine ⟨30005073094143982076043031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160027056502101237738896165 30005073094143982076043031)
        ·
          refine ⟨45007609641215973114064547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30005073094143982076043031 45007609641215973114064547)
          ·
            refine ⟨67511414461823959671096821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45007609641215973114064547 67511414461823959671096821)
            ·
              refine ⟨6329195105795996219165327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67511414461823959671096821 6329195105795996219165327)
              ·
                refine ⟨9493792658693994328747991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329195105795996219165327 9493792658693994328747991)
                ·
                  refine ⟨14240688988040991493121987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493792658693994328747991 14240688988040991493121987)
                  ·
                    refine ⟨21361033482061487239682981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14240688988040991493121987 21361033482061487239682981)
                    ·
                      refine ⟨4005193777886528857440559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21361033482061487239682981 4005193777886528857440559)
                      ·
                        rfl

theorem cell23_7800087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_7800087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800087 prefixEnd_7800087 := by exact prefixLift 7800087
  have htrace : WordTrace (prefixWord ++ tailWord_7800087) baseStart_7800087 baseEnd_7800087 := by
    simpa [prefixWord, tailWord_7800087, baseEnd_7800087] using wordTrace_append hprefix tailTrace_7800087
  have hstable : (prefixWord ++ tailWord_7800087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800087).length < 2 ^ (prefixWord ++ tailWord_7800087).sum := by decide
  have hdescent : baseEnd_7800087 < baseStart_7800087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800090 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_7800090 : Nat := 118140960795 + 7800090 * 2 ^ 59
def prefixEnd_7800090 : Nat := 4983230072969 + 3 ^ 40 * 7800090 * 2
def baseEnd_7800090 : Nat := 4005195318328492345703045

theorem tailTrace_7800090 : CollatzResearch.WordTrace tailWord_7800090 prefixEnd_7800090 4005195318328492345703045 := by
  unfold tailWord_7800090
  simp only [CollatzResearch.WordTrace]
  refine ⟨71123163577903388539821431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189661769541075702772857149 71123163577903388539821431)
  ·
    refine ⟨106684745366855082809732147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71123163577903388539821431 106684745366855082809732147)
    ·
      refine ⟨160027118050282624214598221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106684745366855082809732147 160027118050282624214598221)
      ·
        refine ⟨60010169268855984080474333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160027118050282624214598221 60010169268855984080474333)
        ·
          refine ⟨22503813475820994030177875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60010169268855984080474333 22503813475820994030177875)
          ·
            refine ⟨33755720213731491045266813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22503813475820994030177875 33755720213731491045266813)
            ·
              refine ⟨12658395080149309141975055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33755720213731491045266813 12658395080149309141975055)
              ·
                refine ⟨18987592620223963712962583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12658395080149309141975055 18987592620223963712962583)
                ·
                  refine ⟨28481388930335945569443875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18987592620223963712962583 28481388930335945569443875)
                  ·
                    refine ⟨42722083395503918354165813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28481388930335945569443875 42722083395503918354165813)
                    ·
                      refine ⟨4005195318328492345703045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42722083395503918354165813 4005195318328492345703045)
                      ·
                        rfl

theorem cell23_7800090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_7800090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800090 prefixEnd_7800090 := by exact prefixLift 7800090
  have htrace : WordTrace (prefixWord ++ tailWord_7800090) baseStart_7800090 baseEnd_7800090 := by
    simpa [prefixWord, tailWord_7800090, baseEnd_7800090] using wordTrace_append hprefix tailTrace_7800090
  have hstable : (prefixWord ++ tailWord_7800090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800090).length < 2 ^ (prefixWord ++ tailWord_7800090).sum := by decide
  have hdescent : baseEnd_7800090 < baseStart_7800090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800093 : List Nat := [1, 4, 2, 3, 1, 12]
def baseStart_7800093 : Nat := 118140960795 + 7800093 * 2 ^ 59
def prefixEnd_7800093 : Nat := 4983230072969 + 3 ^ 40 * 7800093 * 2
def baseEnd_7800093 : Nat := 16482291599878419069817

theorem tailTrace_7800093 : CollatzResearch.WordTrace tailWord_7800093 prefixEnd_7800093 16482291599878419069817 := by
  unfold tailWord_7800093
  simp only [CollatzResearch.WordTrace]
  refine ⟨284492763730602685671644933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189661842487068457114429955 284492763730602685671644933)
  ·
    refine ⟨53342393199488003563433425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284492763730602685671644933 53342393199488003563433425)
    ·
      refine ⟨40006794899616002672575069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53342393199488003563433425 40006794899616002672575069)
      ·
        refine ⟨15002548087356001002215651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40006794899616002672575069 15002548087356001002215651)
        ·
          refine ⟨22503822131034001503323477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15002548087356001002215651 22503822131034001503323477)
          ·
            refine ⟨16482291599878419069817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22503822131034001503323477 16482291599878419069817)
            ·
              rfl

theorem cell23_7800093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 12].length) (baseStart_7800093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800093 prefixEnd_7800093 := by exact prefixLift 7800093
  have htrace : WordTrace (prefixWord ++ tailWord_7800093) baseStart_7800093 baseEnd_7800093 := by
    simpa [prefixWord, tailWord_7800093, baseEnd_7800093] using wordTrace_append hprefix tailTrace_7800093
  have hstable : (prefixWord ++ tailWord_7800093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800093).length < 2 ^ (prefixWord ++ tailWord_7800093).sum := by decide
  have hdescent : baseEnd_7800093 < baseStart_7800093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800098 : List Nat := [3, 3, 1, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_7800098 : Nat := 118140960795 + 7800098 * 2 ^ 59
def prefixEnd_7800098 : Nat := 4983230072969 + 3 ^ 40 * 7800098 * 2
def baseEnd_7800098 : Nat := 4005199426173728314403009

theorem tailTrace_7800098 : CollatzResearch.WordTrace tailWord_7800098 prefixEnd_7800098 4005199426173728314403009 := by
  unfold tailWord_7800098
  simp only [CollatzResearch.WordTrace]
  refine ⟨71123236523896142881394237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189661964063723047683717965 71123236523896142881394237)
  ·
    refine ⟨26671213696461053580522839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71123236523896142881394237 26671213696461053580522839)
    ·
      refine ⟨40006820544691580370784259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26671213696461053580522839 40006820544691580370784259)
      ·
        refine ⟨60010230817037370556176389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40006820544691580370784259 60010230817037370556176389)
        ·
          refine ⟨11251918278194506979283073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60010230817037370556176389 11251918278194506979283073)
          ·
            refine ⟨8438938708645880234462305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11251918278194506979283073 8438938708645880234462305)
            ·
              refine ⟨6329204031484410175846729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8438938708645880234462305 6329204031484410175846729)
              ·
                refine ⟨4746903023613307631885047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6329204031484410175846729 4746903023613307631885047)
                ·
                  refine ⟨7120354535419961447827571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746903023613307631885047 7120354535419961447827571)
                  ·
                    refine ⟨10680531803129942171741357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7120354535419961447827571 10680531803129942171741357)
                    ·
                      refine ⟨4005199426173728314403009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680531803129942171741357 4005199426173728314403009)
                      ·
                        rfl

theorem cell23_7800098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_7800098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800098 prefixEnd_7800098 := by exact prefixLift 7800098
  have htrace : WordTrace (prefixWord ++ tailWord_7800098) baseStart_7800098 baseEnd_7800098 := by
    simpa [prefixWord, tailWord_7800098, baseEnd_7800098] using wordTrace_append hprefix tailTrace_7800098
  have hstable : (prefixWord ++ tailWord_7800098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800098).length < 2 ^ (prefixWord ++ tailWord_7800098).sum := by decide
  have hdescent : baseEnd_7800098 < baseStart_7800098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800120 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_7800120 : Nat := 118140960795 + 7800120 * 2 ^ 59
def prefixEnd_7800120 : Nat := 4983230072969 + 3 ^ 40 * 7800120 * 2
def baseEnd_7800120 : Nat := 4005210722748127228327907

theorem tailTrace_7800120 : CollatzResearch.WordTrace tailWord_7800120 prefixEnd_7800120 4005210722748127228327907 := by
  unfold tailWord_7800120
  simp only [CollatzResearch.WordTrace]
  refine ⟨142246874250752434641438907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189662499001003246188585209 142246874250752434641438907)
  ·
    refine ⟨213370311376128651962158361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142246874250752434641438907 213370311376128651962158361)
    ·
      refine ⟨160027733532096488971618771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213370311376128651962158361 160027733532096488971618771)
      ·
        refine ⟨240041600298144733457428157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160027733532096488971618771 240041600298144733457428157)
        ·
          refine ⟨90015600111804275046535559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240041600298144733457428157 90015600111804275046535559)
          ·
            refine ⟨135023400167706412569803339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90015600111804275046535559 135023400167706412569803339)
            ·
              refine ⟨202535100251559618854705009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135023400167706412569803339 202535100251559618854705009)
              ·
                refine ⟨151901325188669714141028757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202535100251559618854705009 151901325188669714141028757)
                ·
                  refine ⟨7120374618218892850360723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151901325188669714141028757 7120374618218892850360723)
                  ·
                    refine ⟨10680561927328339275541085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7120374618218892850360723 10680561927328339275541085)
                    ·
                      refine ⟨4005210722748127228327907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680561927328339275541085 4005210722748127228327907)
                      ·
                        rfl

theorem cell23_7800120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_7800120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800120 prefixEnd_7800120 := by exact prefixLift 7800120
  have htrace : WordTrace (prefixWord ++ tailWord_7800120) baseStart_7800120 baseEnd_7800120 := by
    simpa [prefixWord, tailWord_7800120, baseEnd_7800120] using wordTrace_append hprefix tailTrace_7800120
  have hstable : (prefixWord ++ tailWord_7800120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800120).length < 2 ^ (prefixWord ++ tailWord_7800120).sum := by decide
  have hdescent : baseEnd_7800120 < baseStart_7800120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800141 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_7800141 : Nat := 118140960795 + 7800141 * 2 ^ 59
def prefixEnd_7800141 : Nat := 4983230072969 + 3 ^ 40 * 7800141 * 2
def baseEnd_7800141 : Nat := 4005221505841871646165311

theorem tailTrace_7800141 : CollatzResearch.WordTrace tailWord_7800141 prefixEnd_7800141 4005221505841871646165311 := by
  unfold tailWord_7800141
  simp only [CollatzResearch.WordTrace]
  refine ⟨284494514434428789869392277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189663009622952526579594851 284494514434428789869392277)
  ·
    refine ⟨13335680364113849525127763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 284494514434428789869392277 13335680364113849525127763)
    ·
      refine ⟨20003520546170774287691645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13335680364113849525127763 20003520546170774287691645)
      ·
        refine ⟨7501320204814040357884367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20003520546170774287691645 7501320204814040357884367)
        ·
          refine ⟨11251980307221060536826551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501320204814040357884367 11251980307221060536826551)
          ·
            refine ⟨16877970460831590805239827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11251980307221060536826551 16877970460831590805239827)
            ·
              refine ⟨25316955691247386207859741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16877970460831590805239827 25316955691247386207859741)
              ·
                refine ⟨9493858384217769827947403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25316955691247386207859741 9493858384217769827947403)
                ·
                  refine ⟨14240787576326654741921105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493858384217769827947403 14240787576326654741921105)
                  ·
                    refine ⟨10680590682244991056440829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14240787576326654741921105 10680590682244991056440829)
                    ·
                      refine ⟨4005221505841871646165311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680590682244991056440829 4005221505841871646165311)
                      ·
                        rfl

theorem cell23_7800141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_7800141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800141 prefixEnd_7800141 := by exact prefixLift 7800141
  have htrace : WordTrace (prefixWord ++ tailWord_7800141) baseStart_7800141 baseEnd_7800141 := by
    simpa [prefixWord, tailWord_7800141, baseEnd_7800141] using wordTrace_append hprefix tailTrace_7800141
  have hstable : (prefixWord ++ tailWord_7800141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800141).length < 2 ^ (prefixWord ++ tailWord_7800141).sum := by decide
  have hdescent : baseEnd_7800141 < baseStart_7800141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800147 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 1, 3, 2]
def baseStart_7800147 : Nat := 118140960795 + 7800147 * 2 ^ 59
def prefixEnd_7800147 : Nat := 4983230072969 + 3 ^ 40 * 7800147 * 2
def baseEnd_7800147 : Nat := 4005224586725798622690283

theorem tailTrace_7800147 : CollatzResearch.WordTrace tailWord_7800147 prefixEnd_7800147 4005224586725798622690283 := by
  unfold tailWord_7800147
  simp only [CollatzResearch.WordTrace]
  refine ⟨284494733272407052894110695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189663155514938035262740463 284494733272407052894110695)
  ·
    refine ⟨426742099908610579341166043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284494733272407052894110695 426742099908610579341166043)
    ·
      refine ⟨640113149862915869011749065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426742099908610579341166043 640113149862915869011749065)
      ·
        refine ⟨480084862397186901758811799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640113149862915869011749065 480084862397186901758811799)
        ·
          refine ⟨720127293595780352638217699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480084862397186901758811799 720127293595780352638217699)
          ·
            refine ⟨1080190940393670528957326549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720127293595780352638217699 1080190940393670528957326549)
            ·
              refine ⟨25316975165476653022437341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1080190940393670528957326549 25316975165476653022437341)
              ·
                refine ⟨9493865687053744883414003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25316975165476653022437341 9493865687053744883414003)
                ·
                  refine ⟨14240798530580617325121005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493865687053744883414003 14240798530580617325121005)
                  ·
                    refine ⟨5340299448967731496920377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14240798530580617325121005 5340299448967731496920377)
                    ·
                      refine ⟨4005224586725798622690283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340299448967731496920377 4005224586725798622690283)
                      ·
                        rfl

theorem cell23_7800147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 3, 2].length) (baseStart_7800147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800147 prefixEnd_7800147 := by exact prefixLift 7800147
  have htrace : WordTrace (prefixWord ++ tailWord_7800147) baseStart_7800147 baseEnd_7800147 := by
    simpa [prefixWord, tailWord_7800147, baseEnd_7800147] using wordTrace_append hprefix tailTrace_7800147
  have hstable : (prefixWord ++ tailWord_7800147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800147).length < 2 ^ (prefixWord ++ tailWord_7800147).sum := by decide
  have hdescent : baseEnd_7800147 < baseStart_7800147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800153 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 2, 6]
def baseStart_7800153 : Nat := 118140960795 + 7800153 * 2 ^ 59
def prefixEnd_7800153 : Nat := 4983230072969 + 3 ^ 40 * 7800153 * 2
def baseEnd_7800153 : Nat := 1335075889203241866405085

theorem tailTrace_7800153 : CollatzResearch.WordTrace tailWord_7800153 prefixEnd_7800153 1335075889203241866405085 := by
  unfold tailWord_7800153
  simp only [CollatzResearch.WordTrace]
  refine ⟨284494952110385315918829113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189663301406923543945886075 284494952110385315918829113)
  ·
    refine ⟨213371214082788986939121835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284494952110385315918829113 213371214082788986939121835)
    ·
      refine ⟨320056821124183480408682753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213371214082788986939121835 320056821124183480408682753)
      ·
        refine ⟨240042615843137610306512065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320056821124183480408682753 240042615843137610306512065)
        ·
          refine ⟨180031961882353207729884049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240042615843137610306512065 180031961882353207729884049)
          ·
            refine ⟨135023971411764905797413037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180031961882353207729884049 135023971411764905797413037)
            ·
              refine ⟨50633989279411839674029889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135023971411764905797413037 50633989279411839674029889)
              ·
                refine ⟨37975491959558879755522417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50633989279411839674029889 37975491959558879755522417)
                ·
                  refine ⟨28481618969669159816641813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37975491959558879755522417 28481618969669159816641813)
                  ·
                    refine ⟨1335075889203241866405085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28481618969669159816641813 1335075889203241866405085)
                    ·
                      rfl

theorem cell23_7800153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_7800153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800153 prefixEnd_7800153 := by exact prefixLift 7800153
  have htrace : WordTrace (prefixWord ++ tailWord_7800153) baseStart_7800153 baseEnd_7800153 := by
    simpa [prefixWord, tailWord_7800153, baseEnd_7800153] using wordTrace_append hprefix tailTrace_7800153
  have hstable : (prefixWord ++ tailWord_7800153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800153).length < 2 ^ (prefixWord ++ tailWord_7800153).sum := by decide
  have hdescent : baseEnd_7800153 < baseStart_7800153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800177 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 1, 4, 2]
def baseStart_7800177 : Nat := 118140960795 + 7800177 * 2 ^ 59
def prefixEnd_7800177 : Nat := 4983230072969 + 3 ^ 40 * 7800177 * 2
def baseEnd_7800177 : Nat := 4005239991145433505315145

theorem tailTrace_7800177 : CollatzResearch.WordTrace tailWord_7800177 prefixEnd_7800177 4005239991145433505315145 := by
  unfold tailWord_7800177
  simp only [CollatzResearch.WordTrace]
  refine ⟨284495827462298368017702785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189663884974865578678468523 284495827462298368017702785)
  ·
    refine ⟨213371870596723776013277089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284495827462298368017702785 213371870596723776013277089)
    ·
      refine ⟨160028902947542832009957817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213371870596723776013277089 160028902947542832009957817)
      ·
        refine ⟨120021677210657124007468363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160028902947542832009957817 120021677210657124007468363)
        ·
          refine ⟨180032515815985686011202545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120021677210657124007468363 180032515815985686011202545)
          ·
            refine ⟨135024386861989264508401909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180032515815985686011202545 135024386861989264508401909)
            ·
              refine ⟨12658536268311493547662679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135024386861989264508401909 12658536268311493547662679)
              ·
                refine ⟨18987804402467240321494019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12658536268311493547662679 18987804402467240321494019)
                ·
                  refine ⟨28481706603700860482241029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18987804402467240321494019 28481706603700860482241029)
                  ·
                    refine ⟨5340319988193911340420193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28481706603700860482241029 5340319988193911340420193)
                    ·
                      refine ⟨4005239991145433505315145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340319988193911340420193 4005239991145433505315145)
                      ·
                        rfl

theorem cell23_7800177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_7800177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800177 prefixEnd_7800177 := by exact prefixLift 7800177
  have htrace : WordTrace (prefixWord ++ tailWord_7800177) baseStart_7800177 baseEnd_7800177 := by
    simpa [prefixWord, tailWord_7800177, baseEnd_7800177] using wordTrace_append hprefix tailTrace_7800177
  have hstable : (prefixWord ++ tailWord_7800177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800177).length < 2 ^ (prefixWord ++ tailWord_7800177).sum := by decide
  have hdescent : baseEnd_7800177 < baseStart_7800177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800181 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_7800181 : Nat := 118140960795 + 7800181 * 2 ^ 59
def prefixEnd_7800181 : Nat := 4983230072969 + 3 ^ 40 * 7800181 * 2
def baseEnd_7800181 : Nat := 4005242045068051489665127

theorem tailTrace_7800181 : CollatzResearch.WordTrace tailWord_7800181 prefixEnd_7800181 4005242045068051489665127 := by
  unfold tailWord_7800181
  simp only [CollatzResearch.WordTrace]
  refine ⟨284495973354283876700848397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189663982236189251133898931 284495973354283876700848397)
  ·
    refine ⟨106685990007856453762818149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284495973354283876700848397 106685990007856453762818149)
    ·
      refine ⟨20003623126473085080528403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106685990007856453762818149 20003623126473085080528403)
      ·
        refine ⟨30005434689709627620792605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20003623126473085080528403 30005434689709627620792605)
        ·
          refine ⟨11252038008641110357797227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30005434689709627620792605 11252038008641110357797227)
          ·
            refine ⟨16878057012961665536695841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11252038008641110357797227 16878057012961665536695841)
            ·
              refine ⟨12658542759721249152521881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16878057012961665536695841 12658542759721249152521881)
              ·
                refine ⟨9493907069790936864391411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12658542759721249152521881 9493907069790936864391411)
                ·
                  refine ⟨14240860604686405296587117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493907069790936864391411 14240860604686405296587117)
                  ·
                    refine ⟨5340322726757401986220169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14240860604686405296587117 5340322726757401986220169)
                    ·
                      refine ⟨4005242045068051489665127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340322726757401986220169 4005242045068051489665127)
                      ·
                        rfl

theorem cell23_7800181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_7800181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800181 prefixEnd_7800181 := by exact prefixLift 7800181
  have htrace : WordTrace (prefixWord ++ tailWord_7800181) baseStart_7800181 baseEnd_7800181 := by
    simpa [prefixWord, tailWord_7800181, baseEnd_7800181] using wordTrace_append hprefix tailTrace_7800181
  have hstable : (prefixWord ++ tailWord_7800181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800181).length < 2 ^ (prefixWord ++ tailWord_7800181).sum := by decide
  have hdescent : baseEnd_7800181 < baseStart_7800181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
