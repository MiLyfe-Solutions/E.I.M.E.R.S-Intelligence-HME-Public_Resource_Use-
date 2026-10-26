import V185TrunkScan20Chunk131

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_802029 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_802029 : Nat := 118140960795 + 802029 * 2 ^ 59
def prefixEnd_802029 : Nat := 4983230072969 + 3 ^ 40 * 802029 * 2
def baseEnd_802029 : Nat := 366067889639953592488037

theorem tailTrace_802029 : CollatzResearch.WordTrace tailWord_802029 prefixEnd_802029 366067889639953592488037 := by
  unfold tailWord_802029
  simp only [CollatzResearch.WordTrace]
  refine ⟨29252400811393383493121141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19501600540928922328747427 29252400811393383493121141)
  ·
    refine ⟨2742412576068129702480107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29252400811393383493121141 2742412576068129702480107)
    ·
      refine ⟨4113618864102194553720161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742412576068129702480107 4113618864102194553720161)
      ·
        refine ⟨3085214148076645915290121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4113618864102194553720161 3085214148076645915290121)
        ·
          refine ⟨2313910611057484436467591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3085214148076645915290121 2313910611057484436467591)
          ·
            refine ⟨3470865916586226654701387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313910611057484436467591 3470865916586226654701387)
            ·
              refine ⟨5206298874879339982052081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470865916586226654701387 5206298874879339982052081)
              ·
                refine ⟨3904724156159504986539061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5206298874879339982052081 3904724156159504986539061)
                ·
                  refine ⟨366067889639953592488037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3904724156159504986539061 366067889639953592488037)
                  ·
                    rfl

theorem cell20_802029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_802029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802029 prefixEnd_802029 := by exact prefixLift 802029
  have htrace : WordTrace (prefixWord ++ tailWord_802029) baseStart_802029 baseEnd_802029 := by
    simpa [prefixWord, tailWord_802029, baseEnd_802029] using wordTrace_append hprefix tailTrace_802029
  have hstable : (prefixWord ++ tailWord_802029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802029).length < 2 ^ (prefixWord ++ tailWord_802029).sum := by decide
  have hdescent : baseEnd_802029 < baseStart_802029 := by decide
  rcases family_descends (prefixWord ++ tailWord_802029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802108 : List Nat := [2, 2, 2, 2, 1, 3, 4, 2, 2]
def baseStart_802108 : Nat := 118140960795 + 802108 * 2 ^ 59
def prefixEnd_802108 : Nat := 4983230072969 + 3 ^ 40 * 802108 * 2
def baseEnd_802108 : Nat := 366103947392580428854381

theorem tailTrace_802108 : CollatzResearch.WordTrace tailWord_802108 prefixEnd_802108 366103947392580428854381 := by
  unfold tailWord_802108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14627641089053589992623489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19503521452071453323497985 14627641089053589992623489)
  ·
    refine ⟨10970730816790192494467617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14627641089053589992623489 10970730816790192494467617)
    ·
      refine ⟨8228048112592644370850713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10970730816790192494467617 8228048112592644370850713)
      ·
        refine ⟨6171036084444483278138035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8228048112592644370850713 6171036084444483278138035)
        ·
          refine ⟨9256554126666724917207053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171036084444483278138035 9256554126666724917207053)
          ·
            refine ⟨3471207797500021843952645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9256554126666724917207053 3471207797500021843952645)
            ·
              refine ⟨650851462031254095741121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3471207797500021843952645 650851462031254095741121)
              ·
                refine ⟨488138596523440571805841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650851462031254095741121 488138596523440571805841)
                ·
                  refine ⟨366103947392580428854381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488138596523440571805841 366103947392580428854381)
                  ·
                    rfl

theorem cell20_802108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_802108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802108 prefixEnd_802108 := by exact prefixLift 802108
  have htrace : WordTrace (prefixWord ++ tailWord_802108) baseStart_802108 baseEnd_802108 := by
    simpa [prefixWord, tailWord_802108, baseEnd_802108] using wordTrace_append hprefix tailTrace_802108
  have hstable : (prefixWord ++ tailWord_802108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802108).length < 2 ^ (prefixWord ++ tailWord_802108).sum := by decide
  have hdescent : baseEnd_802108 < baseStart_802108 := by decide
  rcases family_descends (prefixWord ++ tailWord_802108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802119 : List Nat := [1, 1, 4, 1, 2, 3, 3, 5]
def baseStart_802119 : Nat := 118140960795 + 802119 * 2 ^ 59
def prefixEnd_802119 : Nat := 4983230072969 + 3 ^ 40 * 802119 * 2
def baseEnd_802119 : Nat := 122036322697437759829223

theorem tailTrace_802119 : CollatzResearch.WordTrace tailWord_802119 prefixEnd_802119 122036322697437759829223 := by
  unfold tailWord_802119
  simp only [CollatzResearch.WordTrace]
  refine ⟨29255683381067328863897411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19503788920711552575931607 29255683381067328863897411)
  ·
    refine ⟨43883525071600993295846117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29255683381067328863897411 43883525071600993295846117)
    ·
      refine ⟨8228160950925186242971147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43883525071600993295846117 8228160950925186242971147)
      ·
        refine ⟨12342241426387779364456721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8228160950925186242971147 12342241426387779364456721)
        ·
          refine ⟨9256681069790834523342541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12342241426387779364456721 9256681069790834523342541)
          ·
            refine ⟨3471255401171562946253453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9256681069790834523342541 3471255401171562946253453)
            ·
              refine ⟨1301720775439336104845045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3471255401171562946253453 1301720775439336104845045)
              ·
                refine ⟨122036322697437759829223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1301720775439336104845045 122036322697437759829223)
                ·
                  rfl

theorem cell20_802119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_802119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802119 prefixEnd_802119 := by exact prefixLift 802119
  have htrace : WordTrace (prefixWord ++ tailWord_802119) baseStart_802119 baseEnd_802119 := by
    simpa [prefixWord, tailWord_802119, baseEnd_802119] using wordTrace_append hprefix tailTrace_802119
  have hstable : (prefixWord ++ tailWord_802119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802119).length < 2 ^ (prefixWord ++ tailWord_802119).sum := by decide
  have hdescent : baseEnd_802119 < baseStart_802119 := by decide
  rcases family_descends (prefixWord ++ tailWord_802119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802146 : List Nat := [3, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_802146 : Nat := 118140960795 + 802146 * 2 ^ 59
def prefixEnd_802146 : Nat := 4983230072969 + 3 ^ 40 * 802146 * 2
def baseEnd_802146 : Nat := 366121291628021185587559

theorem tailTrace_802146 : CollatzResearch.WordTrace tailWord_802146 prefixEnd_802146 366121291628021185587559 := by
  unfold tailWord_802146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314167037992378118782573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19504445434646341650086861 7314167037992378118782573)
  ·
    refine ⟨2742812639247141794543465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7314167037992378118782573 2742812639247141794543465)
    ·
      refine ⟨2057109479435356345907599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2742812639247141794543465 2057109479435356345907599)
      ·
        refine ⟨3085664219153034518861399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057109479435356345907599 3085664219153034518861399)
        ·
          refine ⟨4628496328729551778292099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3085664219153034518861399 4628496328729551778292099)
          ·
            refine ⟨6942744493094327667438149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628496328729551778292099 6942744493094327667438149)
            ·
              refine ⟨1301764592455186437644653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6942744493094327667438149 1301764592455186437644653)
              ·
                refine ⟨488161722170694914116745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1301764592455186437644653 488161722170694914116745)
                ·
                  refine ⟨366121291628021185587559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488161722170694914116745 366121291628021185587559)
                  ·
                    rfl

theorem cell20_802146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_802146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802146 prefixEnd_802146 := by exact prefixLift 802146
  have htrace : WordTrace (prefixWord ++ tailWord_802146) baseStart_802146 baseEnd_802146 := by
    simpa [prefixWord, tailWord_802146, baseEnd_802146] using wordTrace_append hprefix tailTrace_802146
  have hstable : (prefixWord ++ tailWord_802146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802146).length < 2 ^ (prefixWord ++ tailWord_802146).sum := by decide
  have hdescent : baseEnd_802146 < baseStart_802146 := by decide
  rcases family_descends (prefixWord ++ tailWord_802146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802157 : List Nat := [1, 5, 1, 1, 1, 4, 7]
def baseStart_802157 : Nat := 118140960795 + 802157 * 2 ^ 59
def prefixEnd_802157 : Nat := 4983230072969 + 3 ^ 40 * 802157 * 2
def baseEnd_802157 : Nat := 40680701369750448468983

theorem tailTrace_802157 : CollatzResearch.WordTrace tailWord_802157 prefixEnd_802157 40680701369750448468983 := by
  unfold tailWord_802157
  simp only [CollatzResearch.WordTrace]
  refine ⟨29257069354929661353780725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19504712903286440902520483 29257069354929661353780725)
  ·
    refine ⟨2742850252024655751916943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29257069354929661353780725 2742850252024655751916943)
    ·
      refine ⟨4114275378036983627875415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742850252024655751916943 4114275378036983627875415)
      ·
        refine ⟨6171413067055475441813123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114275378036983627875415 6171413067055475441813123)
        ·
          refine ⟨9257119600583213162719685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171413067055475441813123 9257119600583213162719685)
          ·
            refine ⟨1735709925109352468009941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9257119600583213162719685 1735709925109352468009941)
            ·
              refine ⟨40680701369750448468983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1735709925109352468009941 40680701369750448468983)
              ·
                rfl

theorem cell20_802157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_802157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802157 prefixEnd_802157 := by exact prefixLift 802157
  have htrace : WordTrace (prefixWord ++ tailWord_802157) baseStart_802157 baseEnd_802157 := by
    simpa [prefixWord, tailWord_802157, baseEnd_802157] using wordTrace_append hprefix tailTrace_802157
  have hstable : (prefixWord ++ tailWord_802157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802157).length < 2 ^ (prefixWord ++ tailWord_802157).sum := by decide
  have hdescent : baseEnd_802157 < baseStart_802157 := by decide
  rcases family_descends (prefixWord ++ tailWord_802157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802177 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 3]
def baseStart_802177 : Nat := 118140960795 + 802177 * 2 ^ 59
def prefixEnd_802177 : Nat := 4983230072969 + 3 ^ 40 * 802177 * 2
def baseEnd_802177 : Nat := 366135440872722855554099

theorem tailTrace_802177 : CollatzResearch.WordTrace tailWord_802177 prefixEnd_802177 366135440872722855554099 := by
  unfold tailWord_802177
  simp only [CollatzResearch.WordTrace]
  refine ⟨29257798814857204769508785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19505199209904803179672523 29257798814857204769508785)
  ·
    refine ⟨21943349111142903577131589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29257798814857204769508785 21943349111142903577131589)
    ·
      refine ⟨4114377958339294420712173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21943349111142903577131589 4114377958339294420712173)
      ·
        refine ⟨1542891734377235407767065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4114377958339294420712173 1542891734377235407767065)
        ·
          refine ⟨1157168800782926555825299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1542891734377235407767065 1157168800782926555825299)
          ·
            refine ⟨1735753201174389833737949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157168800782926555825299 1735753201174389833737949)
            ·
              refine ⟨650907450440396187651731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1735753201174389833737949 650907450440396187651731)
              ·
                refine ⟨976361175660594281477597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650907450440396187651731 976361175660594281477597)
                ·
                  refine ⟨366135440872722855554099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976361175660594281477597 366135440872722855554099)
                  ·
                    rfl

theorem cell20_802177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_802177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802177 prefixEnd_802177 := by exact prefixLift 802177
  have htrace : WordTrace (prefixWord ++ tailWord_802177) baseStart_802177 baseEnd_802177 := by
    simpa [prefixWord, tailWord_802177, baseEnd_802177] using wordTrace_append hprefix tailTrace_802177
  have hstable : (prefixWord ++ tailWord_802177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802177).length < 2 ^ (prefixWord ++ tailWord_802177).sum := by decide
  have hdescent : baseEnd_802177 < baseStart_802177 := by decide
  rcases family_descends (prefixWord ++ tailWord_802177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802202 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_802202 : Nat := 118140960795 + 802202 * 2 ^ 59
def prefixEnd_802202 : Nat := 4983230072969 + 3 ^ 40 * 802202 * 2
def baseEnd_802202 : Nat := 366146851553933879720663

theorem tailTrace_802202 : CollatzResearch.WordTrace tailWord_802202 prefixEnd_802202 366146851553933879720663 := by
  unfold tailWord_802202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314677659941658509792215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19505807093177756026112573 7314677659941658509792215)
  ·
    refine ⟨10972016489912487764688323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314677659941658509792215 10972016489912487764688323)
    ·
      refine ⟨16458024734868731647032485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10972016489912487764688323 16458024734868731647032485)
      ·
        refine ⟨3085879637787887183818591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16458024734868731647032485 3085879637787887183818591)
        ·
          refine ⟨4628819456681830775727887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3085879637787887183818591 4628819456681830775727887)
          ·
            refine ⟨6943229185022746163591831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628819456681830775727887 6943229185022746163591831)
            ·
              refine ⟨10414843777534119245387747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943229185022746163591831 10414843777534119245387747)
              ·
                refine ⟨15622265666301178868081621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10414843777534119245387747 15622265666301178868081621)
                ·
                  refine ⟨366146851553933879720663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15622265666301178868081621 366146851553933879720663)
                  ·
                    rfl

theorem cell20_802202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_802202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802202 prefixEnd_802202 := by exact prefixLift 802202
  have htrace : WordTrace (prefixWord ++ tailWord_802202) baseStart_802202 baseEnd_802202 := by
    simpa [prefixWord, tailWord_802202, baseEnd_802202] using wordTrace_append hprefix tailTrace_802202
  have hstable : (prefixWord ++ tailWord_802202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802202).length < 2 ^ (prefixWord ++ tailWord_802202).sum := by decide
  have hdescent : baseEnd_802202 < baseStart_802202 := by decide
  rcases family_descends (prefixWord ++ tailWord_802202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802236 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_802236 : Nat := 118140960795 + 802236 * 2 ^ 59
def prefixEnd_802236 : Nat := 4983230072969 + 3 ^ 40 * 802236 * 2
def baseEnd_802236 : Nat := 366162370080380872587191

theorem tailTrace_802236 : CollatzResearch.WordTrace tailWord_802236 prefixEnd_802236 366162370080380872587191 := by
  unfold tailWord_802236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14629975360821728922953281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19506633814428971897271041 14629975360821728922953281)
  ·
    refine ⟨10972481520616296692214961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14629975360821728922953281 10972481520616296692214961)
    ·
      refine ⟨8229361140462222519161221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10972481520616296692214961 8229361140462222519161221)
      ·
        refine ⟨1543005213836666722342729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8229361140462222519161221 1543005213836666722342729)
        ·
          refine ⟨1157253910377500041757047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1543005213836666722342729 1157253910377500041757047)
          ·
            refine ⟨1735880865566250062635571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157253910377500041757047 1735880865566250062635571)
            ·
              refine ⟨2603821298349375093953357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735880865566250062635571 2603821298349375093953357)
              ·
                refine ⟨976432986881015660232509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2603821298349375093953357 976432986881015660232509)
                ·
                  refine ⟨366162370080380872587191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976432986881015660232509 366162370080380872587191)
                  ·
                    rfl

theorem cell20_802236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_802236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802236 prefixEnd_802236 := by exact prefixLift 802236
  have htrace : WordTrace (prefixWord ++ tailWord_802236) baseStart_802236 baseEnd_802236 := by
    simpa [prefixWord, tailWord_802236, baseEnd_802236] using wordTrace_append hprefix tailTrace_802236
  have hstable : (prefixWord ++ tailWord_802236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802236).length < 2 ^ (prefixWord ++ tailWord_802236).sum := by decide
  have hdescent : baseEnd_802236 < baseStart_802236 := by decide
  rcases family_descends (prefixWord ++ tailWord_802236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802247 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_802247 : Nat := 118140960795 + 802247 * 2 ^ 59
def prefixEnd_802247 : Nat := 4983230072969 + 3 ^ 40 * 802247 * 2
def baseEnd_802247 : Nat := 366167390780113723220479

theorem tailTrace_802247 : CollatzResearch.WordTrace tailWord_802247 prefixEnd_802247 366167390780113723220479 := by
  unfold tailWord_802247
  simp only [CollatzResearch.WordTrace]
  refine ⟨29260351924603606724556995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19506901283069071149704663 29260351924603606724556995)
  ·
    refine ⟨43890527886905410086835493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29260351924603606724556995 43890527886905410086835493)
    ·
      refine ⟨8229473978794764391281655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43890527886905410086835493 8229473978794764391281655)
      ·
        refine ⟨12344210968192146586922483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8229473978794764391281655 12344210968192146586922483)
        ·
          refine ⟨18516316452288219880383725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12344210968192146586922483 18516316452288219880383725)
          ·
            refine ⟨6943618669608082455143897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18516316452288219880383725 6943618669608082455143897)
            ·
              refine ⟨5207714002206061841357923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6943618669608082455143897 5207714002206061841357923)
              ·
                refine ⟨7811571003309092762036885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207714002206061841357923 7811571003309092762036885)
                ·
                  refine ⟨366167390780113723220479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7811571003309092762036885 366167390780113723220479)
                  ·
                    rfl

theorem cell20_802247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_802247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802247 prefixEnd_802247 := by exact prefixLift 802247
  have htrace : WordTrace (prefixWord ++ tailWord_802247) baseStart_802247 baseEnd_802247 := by
    simpa [prefixWord, tailWord_802247, baseEnd_802247] using wordTrace_append hprefix tailTrace_802247
  have hstable : (prefixWord ++ tailWord_802247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802247).length < 2 ^ (prefixWord ++ tailWord_802247).sum := by decide
  have hdescent : baseEnd_802247 < baseStart_802247 := by decide
  rcases family_descends (prefixWord ++ tailWord_802247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802277 : List Nat := [1, 3, 1, 5, 1, 3, 2, 2, 2]
def baseStart_802277 : Nat := 118140960795 + 802277 * 2 ^ 59
def prefixEnd_802277 : Nat := 4983230072969 + 3 ^ 40 * 802277 * 2
def baseEnd_802277 : Nat := 366181083597566952220357

theorem tailTrace_802277 : CollatzResearch.WordTrace tailWord_802277 prefixEnd_802277 366181083597566952220357 := by
  unfold tailWord_802277
  simp only [CollatzResearch.WordTrace]
  refine ⟨29261446114494921848149085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19507630742996614565432723 29261446114494921848149085)
  ·
    refine ⟨10973042292935595693055907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29261446114494921848149085 10973042292935595693055907)
    ·
      refine ⟨16459563439403393539583861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10973042292935595693055907 16459563439403393539583861)
      ·
        refine ⟨1543084072444068144335987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16459563439403393539583861 1543084072444068144335987)
        ·
          refine ⟨2314626108666102216503981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543084072444068144335987 2314626108666102216503981)
          ·
            refine ⟨867984790749788331188993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2314626108666102216503981 867984790749788331188993)
            ·
              refine ⟨650988593062341248391745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867984790749788331188993 650988593062341248391745)
              ·
                refine ⟨488241444796755936293809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650988593062341248391745 488241444796755936293809)
                ·
                  refine ⟨366181083597566952220357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488241444796755936293809 366181083597566952220357)
                  ·
                    rfl

theorem cell20_802277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_802277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802277 prefixEnd_802277 := by exact prefixLift 802277
  have htrace : WordTrace (prefixWord ++ tailWord_802277) baseStart_802277 baseEnd_802277 := by
    simpa [prefixWord, tailWord_802277, baseEnd_802277] using wordTrace_append hprefix tailTrace_802277
  have hstable : (prefixWord ++ tailWord_802277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802277).length < 2 ^ (prefixWord ++ tailWord_802277).sum := by decide
  have hdescent : baseEnd_802277 < baseStart_802277 := by decide
  rcases family_descends (prefixWord ++ tailWord_802277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802381 : List Nat := [1, 6, 1, 1, 4, 1, 6]
def baseStart_802381 : Nat := 118140960795 + 802381 * 2 ^ 59
def prefixEnd_802381 : Nat := 4983230072969 + 3 ^ 40 * 802381 * 2
def baseEnd_802381 : Nat := 40692061336822756972585

theorem tailTrace_802381 : CollatzResearch.WordTrace tailWord_802381 prefixEnd_802381 40692061336822756972585 := by
  unfold tailWord_802381
  simp only [CollatzResearch.WordTrace]
  refine ⟨29265239306118147609934997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19510159537412098406623331 29265239306118147609934997)
  ·
    refine ⟨1371808092474288169215703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29265239306118147609934997 1371808092474288169215703)
    ·
      refine ⟨2057712138711432253823555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371808092474288169215703 2057712138711432253823555)
      ·
        refine ⟨3086568208067148380735333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057712138711432253823555 3086568208067148380735333)
        ·
          refine ⟨578731539012590321387875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3086568208067148380735333 578731539012590321387875)
          ·
            refine ⟨868097308518885482081813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578731539012590321387875 868097308518885482081813)
            ·
              refine ⟨40692061336822756972585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 868097308518885482081813 40692061336822756972585)
              ·
                rfl

theorem cell20_802381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 6].length) (baseStart_802381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802381 prefixEnd_802381 := by exact prefixLift 802381
  have htrace : WordTrace (prefixWord ++ tailWord_802381) baseStart_802381 baseEnd_802381 := by
    simpa [prefixWord, tailWord_802381, baseEnd_802381] using wordTrace_append hprefix tailTrace_802381
  have hstable : (prefixWord ++ tailWord_802381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802381).length < 2 ^ (prefixWord ++ tailWord_802381).sum := by decide
  have hdescent : baseEnd_802381 < baseStart_802381 := by decide
  rcases family_descends (prefixWord ++ tailWord_802381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802392 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_802392 : Nat := 118140960795 + 802392 * 2 ^ 59
def prefixEnd_802392 : Nat := 4983230072969 + 3 ^ 40 * 802392 * 2
def baseEnd_802392 : Nat := 366233572731137663386553

theorem tailTrace_802392 : CollatzResearch.WordTrace tailWord_802392 prefixEnd_802392 366233572731137663386553 := by
  unfold tailWord_802392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632820254539148244292715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19510427006052197659056953 14632820254539148244292715)
  ·
    refine ⟨21949230381808722366439073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14632820254539148244292715 21949230381808722366439073)
    ·
      refine ⟨16461922786356541774829305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21949230381808722366439073 16461922786356541774829305)
      ·
        refine ⟨12346442089767406331121979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16461922786356541774829305 12346442089767406331121979)
        ·
          refine ⟨18519663134651109496682969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12346442089767406331121979 18519663134651109496682969)
          ·
            refine ⟨13889747350988332122512227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18519663134651109496682969 13889747350988332122512227)
            ·
              refine ⟨20834621026482498183768341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13889747350988332122512227 20834621026482498183768341)
              ·
                refine ⟨976622860616367102364141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20834621026482498183768341 976622860616367102364141)
                ·
                  refine ⟨366233572731137663386553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976622860616367102364141 366233572731137663386553)
                  ·
                    rfl

theorem cell20_802392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_802392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802392 prefixEnd_802392 := by exact prefixLift 802392
  have htrace : WordTrace (prefixWord ++ tailWord_802392) baseStart_802392 baseEnd_802392 := by
    simpa [prefixWord, tailWord_802392, baseEnd_802392] using wordTrace_append hprefix tailTrace_802392
  have hstable : (prefixWord ++ tailWord_802392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802392).length < 2 ^ (prefixWord ++ tailWord_802392).sum := by decide
  have hdescent : baseEnd_802392 < baseStart_802392 := by decide
  rcases family_descends (prefixWord ++ tailWord_802392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802409 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 3]
def baseStart_802409 : Nat := 118140960795 + 802409 * 2 ^ 59
def prefixEnd_802409 : Nat := 4983230072969 + 3 ^ 40 * 802409 * 2
def baseEnd_802409 : Nat := 366241331994361159819817

theorem tailTrace_802409 : CollatzResearch.WordTrace tailWord_802409 prefixEnd_802409 366241331994361159819817 := by
  unfold tailWord_802409
  simp only [CollatzResearch.WordTrace]
  refine ⟨29266260550016708391954281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19510840366677805594636187 29266260550016708391954281)
  ·
    refine ⟨21949695412512531293965711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29266260550016708391954281 21949695412512531293965711)
    ·
      refine ⟨32924543118768796940948567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21949695412512531293965711 32924543118768796940948567)
      ·
        refine ⟨49386814678153195411422851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32924543118768796940948567 49386814678153195411422851)
        ·
          refine ⟨74080222017229793117134277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49386814678153195411422851 74080222017229793117134277)
          ·
            refine ⟨13890041628230586209462677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74080222017229793117134277 13890041628230586209462677)
            ·
              refine ⟨651095701323308728568563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13890041628230586209462677 651095701323308728568563)
              ·
                refine ⟨976643551984963092852845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651095701323308728568563 976643551984963092852845)
                ·
                  refine ⟨366241331994361159819817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976643551984963092852845 366241331994361159819817)
                  ·
                    rfl

theorem cell20_802409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_802409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802409 prefixEnd_802409 := by exact prefixLift 802409
  have htrace : WordTrace (prefixWord ++ tailWord_802409) baseStart_802409 baseEnd_802409 := by
    simpa [prefixWord, tailWord_802409, baseEnd_802409] using wordTrace_append hprefix tailTrace_802409
  have hstable : (prefixWord ++ tailWord_802409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802409).length < 2 ^ (prefixWord ++ tailWord_802409).sum := by decide
  have hdescent : baseEnd_802409 < baseStart_802409 := by decide
  rcases family_descends (prefixWord ++ tailWord_802409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802440 : List Nat := [2, 1, 3, 5, 2, 7]
def baseStart_802440 : Nat := 118140960795 + 802440 * 2 ^ 59
def prefixEnd_802440 : Nat := 4983230072969 + 3 ^ 40 * 802440 * 2
def baseEnd_802440 : Nat := 13565017823668993695791

theorem tailTrace_802440 : CollatzResearch.WordTrace tailWord_802440 prefixEnd_802440 13565017823668993695791 := by
  unfold tailWord_802440
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633695606452200343166387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19511594141936267124221849 14633695606452200343166387)
  ·
    refine ⟨21950543409678300514749581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14633695606452200343166387 21950543409678300514749581)
    ·
      refine ⟨8231453778629362693031093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21950543409678300514749581 8231453778629362693031093)
      ·
        refine ⟨771698791746502752471665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8231453778629362693031093 771698791746502752471665)
        ·
          refine ⟨578774093809877064353749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771698791746502752471665 578774093809877064353749)
          ·
            refine ⟨13565017823668993695791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 578774093809877064353749 13565017823668993695791)
            ·
              rfl

theorem cell20_802440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 7].length) (baseStart_802440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802440 prefixEnd_802440 := by exact prefixLift 802440
  have htrace : WordTrace (prefixWord ++ tailWord_802440) baseStart_802440 baseEnd_802440 := by
    simpa [prefixWord, tailWord_802440, baseEnd_802440] using wordTrace_append hprefix tailTrace_802440
  have hstable : (prefixWord ++ tailWord_802440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802440).length < 2 ^ (prefixWord ++ tailWord_802440).sum := by decide
  have hdescent : baseEnd_802440 < baseStart_802440 := by decide
  rcases family_descends (prefixWord ++ tailWord_802440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802450 : List Nat := [3, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_802450 : Nat := 118140960795 + 802450 * 2 ^ 59
def prefixEnd_802450 : Nat := 4983230072969 + 3 ^ 40 * 802450 * 2
def baseEnd_802450 : Nat := 366260045511547239452983

theorem tailTrace_802450 : CollatzResearch.WordTrace tailWord_802450 prefixEnd_802450 366260045511547239452983 := by
  unfold tailWord_802450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316938985717043098549201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19511837295245448262797869 7316938985717043098549201)
  ·
    refine ⟨5487704239287782323911901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7316938985717043098549201 5487704239287782323911901)
    ·
      refine ⟨2057889089732918371466963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5487704239287782323911901 2057889089732918371466963)
      ·
        refine ⟨3086833634599377557200445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057889089732918371466963 3086833634599377557200445)
        ·
          refine ⟨1157562612974766583950167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3086833634599377557200445 1157562612974766583950167)
          ·
            refine ⟨1736343919462149875925251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157562612974766583950167 1736343919462149875925251)
            ·
              refine ⟨2604515879193224813887877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736343919462149875925251 2604515879193224813887877)
              ·
                refine ⟨488346727348729652603977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2604515879193224813887877 488346727348729652603977)
                ·
                  refine ⟨366260045511547239452983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488346727348729652603977 366260045511547239452983)
                  ·
                    rfl

theorem cell20_802450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_802450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802450 prefixEnd_802450 := by exact prefixLift 802450
  have htrace : WordTrace (prefixWord ++ tailWord_802450) baseStart_802450 baseEnd_802450 := by
    simpa [prefixWord, tailWord_802450, baseEnd_802450] using wordTrace_append hprefix tailTrace_802450
  have hstable : (prefixWord ++ tailWord_802450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802450).length < 2 ^ (prefixWord ++ tailWord_802450).sum := by decide
  have hdescent : baseEnd_802450 < baseStart_802450 := by decide
  rcases family_descends (prefixWord ++ tailWord_802450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802482 : List Nat := [3, 2, 1, 1, 1, 2, 2, 8]
def baseStart_802482 : Nat := 118140960795 + 802482 * 2 ^ 59
def prefixEnd_802482 : Nat := 4983230072969 + 3 ^ 40 * 802482 * 2
def baseEnd_802482 : Nat := 122091550394499116795395

theorem tailTrace_802482 : CollatzResearch.WordTrace tailWord_802482 prefixEnd_802482 122091550394499116795395 := by
  unfold tailWord_802482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317230769688060464840425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19512615385834827906241133 7317230769688060464840425)
  ·
    refine ⟨5487923077266045348630319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7317230769688060464840425 5487923077266045348630319)
    ·
      refine ⟨8231884615899068022945479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487923077266045348630319 8231884615899068022945479)
      ·
        refine ⟨12347826923848602034418219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231884615899068022945479 12347826923848602034418219)
        ·
          refine ⟨18521740385772903051627329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347826923848602034418219 18521740385772903051627329)
          ·
            refine ⟨13891305289329677288720497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18521740385772903051627329 13891305289329677288720497)
            ·
              refine ⟨10418478966997257966540373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13891305289329677288720497 10418478966997257966540373)
              ·
                refine ⟨122091550394499116795395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10418478966997257966540373 122091550394499116795395)
                ·
                  rfl

theorem cell20_802482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_802482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802482 prefixEnd_802482 := by exact prefixLift 802482
  have htrace : WordTrace (prefixWord ++ tailWord_802482) baseStart_802482 baseEnd_802482 := by
    simpa [prefixWord, tailWord_802482, baseEnd_802482] using wordTrace_append hprefix tailTrace_802482
  have hstable : (prefixWord ++ tailWord_802482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802482).length < 2 ^ (prefixWord ++ tailWord_802482).sum := by decide
  have hdescent : baseEnd_802482 < baseStart_802482 := by decide
  rcases family_descends (prefixWord ++ tailWord_802482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802509 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 4]
def baseStart_802509 : Nat := 118140960795 + 802509 * 2 ^ 59
def prefixEnd_802509 : Nat := 4983230072969 + 3 ^ 40 * 802509 * 2
def baseEnd_802509 : Nat := 366286974719205256486075

theorem tailTrace_802509 : CollatzResearch.WordTrace tailWord_802509 prefixEnd_802509 366286974719205256486075 := by
  unfold tailWord_802509
  simp only [CollatzResearch.WordTrace]
  refine ⟨29269907849654425470594581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19513271899769616980396387 29269907849654425470594581)
  ·
    refine ⟨1372026930452551193934121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29269907849654425470594581 1372026930452551193934121)
    ·
      refine ⟨1029020197839413395450591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1372026930452551193934121 1029020197839413395450591)
      ·
        refine ⟨1543530296759120093175887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029020197839413395450591 1543530296759120093175887)
        ·
          refine ⟨2315295445138680139763831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543530296759120093175887 2315295445138680139763831)
          ·
            refine ⟨3472943167708020209645747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315295445138680139763831 3472943167708020209645747)
            ·
              refine ⟨5209414751562030314468621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472943167708020209645747 5209414751562030314468621)
              ·
                refine ⟨1953530531835761367925733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5209414751562030314468621 1953530531835761367925733)
                ·
                  refine ⟨366286974719205256486075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953530531835761367925733 366286974719205256486075)
                  ·
                    rfl

theorem cell20_802509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_802509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802509 prefixEnd_802509 := by exact prefixLift 802509
  have htrace : WordTrace (prefixWord ++ tailWord_802509) baseStart_802509 baseEnd_802509 := by
    simpa [prefixWord, tailWord_802509, baseEnd_802509] using wordTrace_append hprefix tailTrace_802509
  have hstable : (prefixWord ++ tailWord_802509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802509).length < 2 ^ (prefixWord ++ tailWord_802509).sum := by decide
  have hdescent : baseEnd_802509 < baseStart_802509 := by decide
  rcases family_descends (prefixWord ++ tailWord_802509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802513 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_802513 : Nat := 118140960795 + 802513 * 2 ^ 59
def prefixEnd_802513 : Nat := 4983230072969 + 3 ^ 40 * 802513 * 2
def baseEnd_802513 : Nat := 366288800428199020352725

theorem tailTrace_802513 : CollatzResearch.WordTrace tailWord_802513 prefixEnd_802513 366288800428199020352725 := by
  unfold tailWord_802513
  simp only [CollatzResearch.WordTrace]
  refine ⟨29270053741639934153740193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19513369161093289435826795 29270053741639934153740193)
  ·
    refine ⟨21952540306229950615305145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29270053741639934153740193 21952540306229950615305145)
    ·
      refine ⟨16464405229672462961478859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21952540306229950615305145 16464405229672462961478859)
      ·
        refine ⟨24696607844508694442218289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16464405229672462961478859 24696607844508694442218289)
        ·
          refine ⟨18522455883381520831663717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24696607844508694442218289 18522455883381520831663717)
          ·
            refine ⟨3472960478134035155936947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18522455883381520831663717 3472960478134035155936947)
            ·
              refine ⟨5209440717201052733905421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472960478134035155936947 5209440717201052733905421)
              ·
                refine ⟨1953540268950394775214533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5209440717201052733905421 1953540268950394775214533)
                ·
                  refine ⟨366288800428199020352725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953540268950394775214533 366288800428199020352725)
                  ·
                    rfl

theorem cell20_802513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_802513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802513 prefixEnd_802513 := by exact prefixLift 802513
  have htrace : WordTrace (prefixWord ++ tailWord_802513) baseStart_802513 baseEnd_802513 := by
    simpa [prefixWord, tailWord_802513, baseEnd_802513] using wordTrace_append hprefix tailTrace_802513
  have hstable : (prefixWord ++ tailWord_802513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802513).length < 2 ^ (prefixWord ++ tailWord_802513).sum := by decide
  have hdescent : baseEnd_802513 < baseStart_802513 := by decide
  rcases family_descends (prefixWord ++ tailWord_802513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802520 : List Nat := [2, 1, 2, 2, 3, 1, 2, 7]
def baseStart_802520 : Nat := 118140960795 + 802520 * 2 ^ 59
def prefixEnd_802520 : Nat := 4983230072969 + 3 ^ 40 * 802520 * 2
def baseEnd_802520 : Nat := 122097331806312702373121

theorem tailTrace_802520 : CollatzResearch.WordTrace tailWord_802520 prefixEnd_802520 122097331806312702373121 := by
  unfold tailWord_802520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14635154526307287174622507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19513539368409716232830009 14635154526307287174622507)
  ·
    refine ⟨21952731789460930761933761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14635154526307287174622507 21952731789460930761933761)
    ·
      refine ⟨16464548842095698071450321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21952731789460930761933761 16464548842095698071450321)
      ·
        refine ⟨12348411631571773553587741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16464548842095698071450321 12348411631571773553587741)
        ·
          refine ⟨4630654361839415082595403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12348411631571773553587741 4630654361839415082595403)
          ·
            refine ⟨6945981542759122623893105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630654361839415082595403 6945981542759122623893105)
            ·
              refine ⟨5209486157069341967919829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6945981542759122623893105 5209486157069341967919829)
              ·
                refine ⟨122097331806312702373121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5209486157069341967919829 122097331806312702373121)
                ·
                  rfl

theorem cell20_802520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_802520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802520 prefixEnd_802520 := by exact prefixLift 802520
  have htrace : WordTrace (prefixWord ++ tailWord_802520) baseStart_802520 baseEnd_802520 := by
    simpa [prefixWord, tailWord_802520, baseEnd_802520] using wordTrace_append hprefix tailTrace_802520
  have hstable : (prefixWord ++ tailWord_802520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802520).length < 2 ^ (prefixWord ++ tailWord_802520).sum := by decide
  have hdescent : baseEnd_802520 < baseStart_802520 := by decide
  rcases family_descends (prefixWord ++ tailWord_802520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802564 : List Nat := [2, 3, 2, 2, 1, 3, 3, 2, 2]
def baseStart_802564 : Nat := 118140960795 + 802564 * 2 ^ 59
def prefixEnd_802564 : Nat := 4983230072969 + 3 ^ 40 * 802564 * 2
def baseEnd_802564 : Nat := 366312078217869509652517

theorem tailTrace_802564 : CollatzResearch.WordTrace tailWord_802564 prefixEnd_802564 366312078217869509652517 := by
  unfold tailWord_802564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14635956932227584931923373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19514609242970113242564497 14635956932227584931923373)
  ·
    refine ⟨5488483849585344349471265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14635956932227584931923373 5488483849585344349471265)
    ·
      refine ⟨4116362887189008262103449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5488483849585344349471265 4116362887189008262103449)
      ·
        refine ⟨3087272165391756196577587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116362887189008262103449 3087272165391756196577587)
        ·
          refine ⟨4630908248087634294866381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087272165391756196577587 4630908248087634294866381)
          ·
            refine ⟨1736590593032862860574893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4630908248087634294866381 1736590593032862860574893)
            ·
              refine ⟨651221472387323572715585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1736590593032862860574893 651221472387323572715585)
              ·
                refine ⟨488416104290492679536689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651221472387323572715585 488416104290492679536689)
                ·
                  refine ⟨366312078217869509652517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488416104290492679536689 366312078217869509652517)
                  ·
                    rfl

theorem cell20_802564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_802564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802564 prefixEnd_802564 := by exact prefixLift 802564
  have htrace : WordTrace (prefixWord ++ tailWord_802564) baseStart_802564 baseEnd_802564 := by
    simpa [prefixWord, tailWord_802564, baseEnd_802564] using wordTrace_append hprefix tailTrace_802564
  have hstable : (prefixWord ++ tailWord_802564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802564).length < 2 ^ (prefixWord ++ tailWord_802564).sum := by decide
  have hdescent : baseEnd_802564 < baseStart_802564 := by decide
  rcases family_descends (prefixWord ++ tailWord_802564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802578 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_802578 : Nat := 118140960795 + 802578 * 2 ^ 59
def prefixEnd_802578 : Nat := 4983230072969 + 3 ^ 40 * 802578 * 2
def baseEnd_802578 : Nat := 366318468199347683185793

theorem tailTrace_802578 : CollatzResearch.WordTrace tailWord_802578 prefixEnd_802578 366318468199347683185793 := by
  unfold tailWord_802578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318106121601112563714097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19514949657602966836570925 7318106121601112563714097)
  ·
    refine ⟨5488579591200834422785573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7318106121601112563714097 5488579591200834422785573)
    ·
      refine ⟨1029108673350156454272295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5488579591200834422785573 1029108673350156454272295)
      ·
        refine ⟨1543663010025234681408443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029108673350156454272295 1543663010025234681408443)
        ·
          refine ⟨2315494515037852022112665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543663010025234681408443 2315494515037852022112665)
          ·
            refine ⟨1736620886278389016584499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315494515037852022112665 1736620886278389016584499)
            ·
              refine ⟨2604931329417583524876749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736620886278389016584499 2604931329417583524876749)
              ·
                refine ⟨976849248531593821828781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2604931329417583524876749 976849248531593821828781)
                ·
                  refine ⟨366318468199347683185793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976849248531593821828781 366318468199347683185793)
                  ·
                    rfl

theorem cell20_802578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_802578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802578 prefixEnd_802578 := by exact prefixLift 802578
  have htrace : WordTrace (prefixWord ++ tailWord_802578) baseStart_802578 baseEnd_802578 := by
    simpa [prefixWord, tailWord_802578, baseEnd_802578] using wordTrace_append hprefix tailTrace_802578
  have hstable : (prefixWord ++ tailWord_802578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802578).length < 2 ^ (prefixWord ++ tailWord_802578).sum := by decide
  have hdescent : baseEnd_802578 < baseStart_802578 := by decide
  rcases family_descends (prefixWord ++ tailWord_802578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802613 : List Nat := [1, 3, 3, 1, 5, 7]
def baseStart_802613 : Nat := 118140960795 + 802613 * 2 ^ 59
def prefixEnd_802613 : Nat := 4983230072969 + 3 ^ 40 * 802613 * 2
def baseEnd_802613 : Nat := 13567942339001596926629

theorem tailTrace_802613 : CollatzResearch.WordTrace tailWord_802613 prefixEnd_802613 13567942339001596926629 := by
  unfold tailWord_802613
  simp only [CollatzResearch.WordTrace]
  refine ⟨29273701041277651232380493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19515800694185100821586995 29273701041277651232380493)
  ·
    refine ⟨10977637890479119212142685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29273701041277651232380493 10977637890479119212142685)
    ·
      refine ⟨4116614208929669704553507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10977637890479119212142685 4116614208929669704553507)
      ·
        refine ⟨6174921313394504556830261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116614208929669704553507 6174921313394504556830261)
        ·
          refine ⟨578898873130734802202837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6174921313394504556830261 578898873130734802202837)
          ·
            refine ⟨13567942339001596926629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 578898873130734802202837 13567942339001596926629)
            ·
              rfl

theorem cell20_802613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 7].length) (baseStart_802613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802613 prefixEnd_802613 := by exact prefixLift 802613
  have htrace : WordTrace (prefixWord ++ tailWord_802613) baseStart_802613 baseEnd_802613 := by
    simpa [prefixWord, tailWord_802613, baseEnd_802613] using wordTrace_append hprefix tailTrace_802613
  have hstable : (prefixWord ++ tailWord_802613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802613).length < 2 ^ (prefixWord ++ tailWord_802613).sum := by decide
  have hdescent : baseEnd_802613 < baseStart_802613 := by decide
  rcases family_descends (prefixWord ++ tailWord_802613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802620 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_802620 : Nat := 118140960795 + 802620 * 2 ^ 59
def prefixEnd_802620 : Nat := 4983230072969 + 3 ^ 40 * 802620 * 2
def baseEnd_802620 : Nat := 366337638143782203785621

theorem tailTrace_802620 : CollatzResearch.WordTrace tailWord_802620 prefixEnd_802620 366337638143782203785621 := by
  unfold tailWord_802620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14636978176126145713942657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19515970901501527618590209 14636978176126145713942657)
  ·
    refine ⟨10977733632094609285456993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14636978176126145713942657 10977733632094609285456993)
    ·
      refine ⟨8233300224070956964092745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10977733632094609285456993 8233300224070956964092745)
      ·
        refine ⟨6174975168053217723069559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8233300224070956964092745 6174975168053217723069559)
        ·
          refine ⟨9262462752079826584604339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174975168053217723069559 9262462752079826584604339)
          ·
            refine ⟨13893694128119739876906509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9262462752079826584604339 13893694128119739876906509)
            ·
              refine ⟨5210135298044902453839941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13893694128119739876906509 5210135298044902453839941)
              ·
                refine ⟨976900368383419210094989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5210135298044902453839941 976900368383419210094989)
                ·
                  refine ⟨366337638143782203785621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976900368383419210094989 366337638143782203785621)
                  ·
                    rfl

theorem cell20_802620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_802620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802620 prefixEnd_802620 := by exact prefixLift 802620
  have htrace : WordTrace (prefixWord ++ tailWord_802620) baseStart_802620 baseEnd_802620 := by
    simpa [prefixWord, tailWord_802620, baseEnd_802620] using wordTrace_append hprefix tailTrace_802620
  have hstable : (prefixWord ++ tailWord_802620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802620).length < 2 ^ (prefixWord ++ tailWord_802620).sum := by decide
  have hdescent : baseEnd_802620 < baseStart_802620 := by decide
  rcases family_descends (prefixWord ++ tailWord_802620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802623 : List Nat := [1, 1, 2, 2, 6, 1, 1, 4, 2]
def baseStart_802623 : Nat := 118140960795 + 802623 * 2 ^ 59
def prefixEnd_802623 : Nat := 4983230072969 + 3 ^ 40 * 802623 * 2
def baseEnd_802623 : Nat := 366339007425527526685609

theorem tailTrace_802623 : CollatzResearch.WordTrace tailWord_802623 prefixEnd_802623 366339007425527526685609 := by
  unfold tailWord_802623
  simp only [CollatzResearch.WordTrace]
  refine ⟨29274065771241422940244523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19516043847494281960163015 29274065771241422940244523)
  ·
    refine ⟨43911098656862134410366785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29274065771241422940244523 43911098656862134410366785)
    ·
      refine ⟨32933323992646600807775089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43911098656862134410366785 32933323992646600807775089)
      ·
        refine ⟨24699992994484950605831317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32933323992646600807775089 24699992994484950605831317)
        ·
          refine ⟨1157812171616482059648343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24699992994484950605831317 1157812171616482059648343)
          ·
            refine ⟨1736718257424723089472515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157812171616482059648343 1736718257424723089472515)
            ·
              refine ⟨2605077386137084634208773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736718257424723089472515 2605077386137084634208773)
              ·
                refine ⟨488452009900703368914145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2605077386137084634208773 488452009900703368914145)
                ·
                  refine ⟨366339007425527526685609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488452009900703368914145 366339007425527526685609)
                  ·
                    rfl

theorem cell20_802623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 2].length) (baseStart_802623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802623 prefixEnd_802623 := by exact prefixLift 802623
  have htrace : WordTrace (prefixWord ++ tailWord_802623) baseStart_802623 baseEnd_802623 := by
    simpa [prefixWord, tailWord_802623, baseEnd_802623] using wordTrace_append hprefix tailTrace_802623
  have hstable : (prefixWord ++ tailWord_802623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802623).length < 2 ^ (prefixWord ++ tailWord_802623).sum := by decide
  have hdescent : baseEnd_802623 < baseStart_802623 := by decide
  rcases family_descends (prefixWord ++ tailWord_802623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802644 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_802644 : Nat := 118140960795 + 802644 * 2 ^ 59
def prefixEnd_802644 : Nat := 4983230072969 + 3 ^ 40 * 802644 * 2
def baseEnd_802644 : Nat := 366348592397744786985523

theorem tailTrace_802644 : CollatzResearch.WordTrace tailWord_802644 prefixEnd_802644 366348592397744786985523 := by
  unfold tailWord_802644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14637415852082671763379493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19516554469443562351172657 14637415852082671763379493)
  ·
    refine ⟨2744515472265500955633655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14637415852082671763379493 2744515472265500955633655)
    ·
      refine ⟨4116773208398251433450483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744515472265500955633655 4116773208398251433450483)
      ·
        refine ⟨6175159812597377150175725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116773208398251433450483 6175159812597377150175725)
        ·
          refine ⟨2315684929724016431315897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6175159812597377150175725 2315684929724016431315897)
          ·
            refine ⟨1736763697293012323486923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315684929724016431315897 1736763697293012323486923)
            ·
              refine ⟨2605145545939518485230385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736763697293012323486923 2605145545939518485230385)
              ·
                refine ⟨1953859159454638863922789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2605145545939518485230385 1953859159454638863922789)
                ·
                  refine ⟨366348592397744786985523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953859159454638863922789 366348592397744786985523)
                  ·
                    rfl

theorem cell20_802644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_802644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802644 prefixEnd_802644 := by exact prefixLift 802644
  have htrace : WordTrace (prefixWord ++ tailWord_802644) baseStart_802644 baseEnd_802644 := by
    simpa [prefixWord, tailWord_802644, baseEnd_802644] using wordTrace_append hprefix tailTrace_802644
  have hstable : (prefixWord ++ tailWord_802644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802644).length < 2 ^ (prefixWord ++ tailWord_802644).sum := by decide
  have hdescent : baseEnd_802644 < baseStart_802644 := by decide
  rcases family_descends (prefixWord ++ tailWord_802644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802682 : List Nat := [3, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_802682 : Nat := 118140960795 + 802682 * 2 ^ 59
def prefixEnd_802682 : Nat := 4983230072969 + 3 ^ 40 * 802682 * 2
def baseEnd_802682 : Nat := 366365936633185543718701

theorem tailTrace_802682 : CollatzResearch.WordTrace tailWord_802682 prefixEnd_802682 366365936633185543718701 := by
  unfold tailWord_802682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319054419506919004160575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19517478452018450677761533 7319054419506919004160575)
  ·
    refine ⟨10978581629260378506240863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7319054419506919004160575 10978581629260378506240863)
    ·
      refine ⟨16467872443890567759361295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10978581629260378506240863 16467872443890567759361295)
      ·
        refine ⟨24701808665835851639041943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16467872443890567759361295 24701808665835851639041943)
        ·
          refine ⟨37052712998753777458562915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24701808665835851639041943 37052712998753777458562915)
          ·
            refine ⟨55579069498130666187844373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37052712998753777458562915 55579069498130666187844373)
            ·
              refine ⟨2605268882724874977555205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55579069498130666187844373 2605268882724874977555205)
              ·
                refine ⟨488487915510914058291601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2605268882724874977555205 488487915510914058291601)
                ·
                  refine ⟨366365936633185543718701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488487915510914058291601 366365936633185543718701)
                  ·
                    rfl

theorem cell20_802682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_802682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802682 prefixEnd_802682 := by exact prefixLift 802682
  have htrace : WordTrace (prefixWord ++ tailWord_802682) baseStart_802682 baseEnd_802682 := by
    simpa [prefixWord, tailWord_802682, baseEnd_802682] using wordTrace_append hprefix tailTrace_802682
  have hstable : (prefixWord ++ tailWord_802682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802682).length < 2 ^ (prefixWord ++ tailWord_802682).sum := by decide
  have hdescent : baseEnd_802682 < baseStart_802682 := by decide
  rcases family_descends (prefixWord ++ tailWord_802682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802702 : List Nat := [4, 1, 1, 5, 2, 1, 2, 4]
def baseStart_802702 : Nat := 118140960795 + 802702 * 2 ^ 59
def prefixEnd_802702 : Nat := 4983230072969 + 3 ^ 40 * 802702 * 2
def baseEnd_802702 : Nat := 122125021726051454350651

theorem tailTrace_802702 : CollatzResearch.WordTrace tailWord_802702 prefixEnd_802702 122125021726051454350651 := by
  unfold tailWord_802702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659618392244402429046295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19517964758636812954913573 3659618392244402429046295)
  ·
    refine ⟨5489427588366603643569443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3659618392244402429046295 5489427588366603643569443)
    ·
      refine ⟨8234141382549905465354165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5489427588366603643569443 8234141382549905465354165)
      ·
        refine ⟨771950754614053637376953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8234141382549905465354165 771950754614053637376953)
        ·
          refine ⟨578963065960540228032715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771950754614053637376953 578963065960540228032715)
          ·
            refine ⟨868444598940810342049073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578963065960540228032715 868444598940810342049073)
            ·
              refine ⟨651333449205607756536805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868444598940810342049073 651333449205607756536805)
              ·
                refine ⟨122125021726051454350651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651333449205607756536805 122125021726051454350651)
                ·
                  rfl

theorem cell20_802702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_802702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802702 prefixEnd_802702 := by exact prefixLift 802702
  have htrace : WordTrace (prefixWord ++ tailWord_802702) baseStart_802702 baseEnd_802702 := by
    simpa [prefixWord, tailWord_802702, baseEnd_802702] using wordTrace_append hprefix tailTrace_802702
  have hstable : (prefixWord ++ tailWord_802702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802702).length < 2 ^ (prefixWord ++ tailWord_802702).sum := by decide
  have hdescent : baseEnd_802702 < baseStart_802702 := by decide
  rcases family_descends (prefixWord ++ tailWord_802702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802706 : List Nat := [3, 2, 3, 2, 1, 1, 4, 4]
def baseStart_802706 : Nat := 118140960795 + 802706 * 2 ^ 59
def prefixEnd_802706 : Nat := 4983230072969 + 3 ^ 40 * 802706 * 2
def baseEnd_802706 : Nat := 122125630295716042306201

theorem tailTrace_802706 : CollatzResearch.WordTrace tailWord_802706 prefixEnd_802706 122125630295716042306201 := by
  unfold tailWord_802706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319273257485182028878993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19518062019960485410343981 7319273257485182028878993)
  ·
    refine ⟨5489454943113886521659245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7319273257485182028878993 5489454943113886521659245)
    ·
      refine ⟨2058545603667707445622217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5489454943113886521659245 2058545603667707445622217)
      ·
        refine ⟨1543909202750780584216663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2058545603667707445622217 1543909202750780584216663)
        ·
          refine ⟨2315863804126170876324995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543909202750780584216663 2315863804126170876324995)
          ·
            refine ⟨3473795706189256314487493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315863804126170876324995 3473795706189256314487493)
            ·
              refine ⟨651336694910485558966405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3473795706189256314487493 651336694910485558966405)
              ·
                refine ⟨122125630295716042306201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651336694910485558966405 122125630295716042306201)
                ·
                  rfl

theorem cell20_802706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_802706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802706 prefixEnd_802706 := by exact prefixLift 802706
  have htrace : WordTrace (prefixWord ++ tailWord_802706) baseStart_802706 baseEnd_802706 := by
    simpa [prefixWord, tailWord_802706, baseEnd_802706] using wordTrace_append hprefix tailTrace_802706
  have hstable : (prefixWord ++ tailWord_802706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802706).length < 2 ^ (prefixWord ++ tailWord_802706).sum := by decide
  have hdescent : baseEnd_802706 < baseStart_802706 := by decide
  rcases family_descends (prefixWord ++ tailWord_802706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802716 : List Nat := [2, 2, 3, 3, 1, 3, 1, 3, 2]
def baseStart_802716 : Nat := 118140960795 + 802716 * 2 ^ 59
def prefixEnd_802716 : Nat := 4983230072969 + 3 ^ 40 * 802716 * 2
def baseEnd_802716 : Nat := 366381455159632536585229

theorem tailTrace_802716 : CollatzResearch.WordTrace tailWord_802716 prefixEnd_802716 366381455159632536585229 := by
  unfold tailWord_802716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638728879952249911690001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19518305173269666548920001 14638728879952249911690001)
  ·
    refine ⟨10979046659964187433767501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14638728879952249911690001 10979046659964187433767501)
    ·
      refine ⟨4117142497486570287662813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10979046659964187433767501 4117142497486570287662813)
      ·
        refine ⟨1543928436557463857873555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4117142497486570287662813 1543928436557463857873555)
        ·
          refine ⟨2315892654836195786810333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543928436557463857873555 2315892654836195786810333)
          ·
            refine ⟨868459745563573420053875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2315892654836195786810333 868459745563573420053875)
            ·
              refine ⟨1302689618345360130080813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868459745563573420053875 1302689618345360130080813)
              ·
                refine ⟨488508606879510048780305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1302689618345360130080813 488508606879510048780305)
                ·
                  refine ⟨366381455159632536585229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488508606879510048780305 366381455159632536585229)
                  ·
                    rfl

theorem cell20_802716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_802716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802716 prefixEnd_802716 := by exact prefixLift 802716
  have htrace : WordTrace (prefixWord ++ tailWord_802716) baseStart_802716 baseEnd_802716 := by
    simpa [prefixWord, tailWord_802716, baseEnd_802716] using wordTrace_append hprefix tailTrace_802716
  have hstable : (prefixWord ++ tailWord_802716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802716).length < 2 ^ (prefixWord ++ tailWord_802716).sum := by decide
  have hdescent : baseEnd_802716 < baseStart_802716 := by decide
  rcases family_descends (prefixWord ++ tailWord_802716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802727 : List Nat := [1, 1, 6, 1, 2, 3, 6]
def baseStart_802727 : Nat := 118140960795 + 802727 * 2 ^ 59
def prefixEnd_802727 : Nat := 4983230072969 + 3 ^ 40 * 802727 * 2
def baseEnd_802727 : Nat := 40709608428818376357613

theorem tailTrace_802727 : CollatzResearch.WordTrace tailWord_802727 prefixEnd_802727 40709608428818376357613 := by
  unfold tailWord_802727
  simp only [CollatzResearch.WordTrace]
  refine ⟨29277858962864648702030435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19518572641909765801353623 29277858962864648702030435)
  ·
    refine ⟨43916788444296973053045653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29277858962864648702030435 43916788444296973053045653)
    ·
      refine ⟨2058599458326420611861515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43916788444296973053045653 2058599458326420611861515)
      ·
        refine ⟨3087899187489630917792273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058599458326420611861515 3087899187489630917792273)
        ·
          refine ⟨2315924390617223188344205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3087899187489630917792273 2315924390617223188344205)
          ·
            refine ⟨868471646481458695629077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2315924390617223188344205 868471646481458695629077)
            ·
              refine ⟨40709608428818376357613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 868471646481458695629077 40709608428818376357613)
              ·
                rfl

theorem cell20_802727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 6].length) (baseStart_802727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802727 prefixEnd_802727 := by exact prefixLift 802727
  have htrace : WordTrace (prefixWord ++ tailWord_802727) baseStart_802727 baseEnd_802727 := by
    simpa [prefixWord, tailWord_802727, baseEnd_802727] using wordTrace_append hprefix tailTrace_802727
  have hstable : (prefixWord ++ tailWord_802727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802727).length < 2 ^ (prefixWord ++ tailWord_802727).sum := by decide
  have hdescent : baseEnd_802727 < baseStart_802727 := by decide
  rcases family_descends (prefixWord ++ tailWord_802727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802817 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_802817 : Nat := 118140960795 + 802817 * 2 ^ 59
def prefixEnd_802817 : Nat := 4983230072969 + 3 ^ 40 * 802817 * 2
def baseEnd_802817 : Nat := 366427554311725074218149

theorem tailTrace_802817 : CollatzResearch.WordTrace tailWord_802817 prefixEnd_802817 366427554311725074218149 := by
  unfold tailWord_802817
  simp only [CollatzResearch.WordTrace]
  refine ⟨29281141532538594072806705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19520761021692396048537803 29281141532538594072806705)
  ·
    refine ⟨21960856149403945554605029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29281141532538594072806705 21960856149403945554605029)
    ·
      refine ⟨4117660528013239791488443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21960856149403945554605029 4117660528013239791488443)
      ·
        refine ⟨6176490792019859687232665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117660528013239791488443 6176490792019859687232665)
        ·
          refine ⟨4632368094014894765424499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6176490792019859687232665 4632368094014894765424499)
          ·
            refine ⟨6948552141022342148136749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632368094014894765424499 6948552141022342148136749)
            ·
              refine ⟨2605707052883378305551281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6948552141022342148136749 2605707052883378305551281)
              ·
                refine ⟨1954280289662533729163461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2605707052883378305551281 1954280289662533729163461)
                ·
                  refine ⟨366427554311725074218149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954280289662533729163461 366427554311725074218149)
                  ·
                    rfl

theorem cell20_802817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_802817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802817 prefixEnd_802817 := by exact prefixLift 802817
  have htrace : WordTrace (prefixWord ++ tailWord_802817) baseStart_802817 baseEnd_802817 := by
    simpa [prefixWord, tailWord_802817, baseEnd_802817] using wordTrace_append hprefix tailTrace_802817
  have hstable : (prefixWord ++ tailWord_802817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802817).length < 2 ^ (prefixWord ++ tailWord_802817).sum := by decide
  have hdescent : baseEnd_802817 < baseStart_802817 := by decide
  rcases family_descends (prefixWord ++ tailWord_802817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802865 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 3]
def baseStart_802865 : Nat := 118140960795 + 802865 * 2 ^ 59
def prefixEnd_802865 : Nat := 4983230072969 + 3 ^ 40 * 802865 * 2
def baseEnd_802865 : Nat := 366449462819650240617953

theorem tailTrace_802865 : CollatzResearch.WordTrace tailWord_802865 prefixEnd_802865 366449462819650240617953 := by
  unfold tailWord_802865
  simp only [CollatzResearch.WordTrace]
  refine ⟨29282892236364698270554049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19521928157576465513702699 29282892236364698270554049)
  ·
    refine ⟨21962169177273523702915537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29282892236364698270554049 21962169177273523702915537)
    ·
      refine ⟨16471626882955142777186653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21962169177273523702915537 16471626882955142777186653)
      ·
        refine ⟨6176860081108178541444995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16471626882955142777186653 6176860081108178541444995)
        ·
          refine ⟨9265290121662267812167493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176860081108178541444995 9265290121662267812167493)
          ·
            refine ⟨1737241897811675214781405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9265290121662267812167493 1737241897811675214781405)
            ·
              refine ⟨651465711679378205543027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1737241897811675214781405 651465711679378205543027)
              ·
                refine ⟨977198567519067308314541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651465711679378205543027 977198567519067308314541)
                ·
                  refine ⟨366449462819650240617953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977198567519067308314541 366449462819650240617953)
                  ·
                    rfl

theorem cell20_802865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_802865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802865 prefixEnd_802865 := by exact prefixLift 802865
  have htrace : WordTrace (prefixWord ++ tailWord_802865) baseStart_802865 baseEnd_802865 := by
    simpa [prefixWord, tailWord_802865, baseEnd_802865] using wordTrace_append hprefix tailTrace_802865
  have hstable : (prefixWord ++ tailWord_802865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802865).length < 2 ^ (prefixWord ++ tailWord_802865).sum := by decide
  have hdescent : baseEnd_802865 < baseStart_802865 := by decide
  rcases family_descends (prefixWord ++ tailWord_802865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802924 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_802924 : Nat := 118140960795 + 802924 * 2 ^ 59
def prefixEnd_802924 : Nat := 4983230072969 + 3 ^ 40 * 802924 * 2
def baseEnd_802924 : Nat := 366476392027308257651045

theorem tailTrace_802924 : CollatzResearch.WordTrace tailWord_802924 prefixEnd_802924 366476392027308257651045 := by
  unfold tailWord_802924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642522071575475673475913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19523362762100634231301217 14642522071575475673475913)
  ·
    refine ⟨10981891553681606755106935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14642522071575475673475913 10981891553681606755106935)
    ·
      refine ⟨16472837330522410132660403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10981891553681606755106935 16472837330522410132660403)
      ·
        refine ⟨24709255995783615198990605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16472837330522410132660403 24709255995783615198990605)
        ·
          refine ⟨9265970998418855699621477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24709255995783615198990605 9265970998418855699621477)
          ·
            refine ⟨1737369562203535443679027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9265970998418855699621477 1737369562203535443679027)
            ·
              refine ⟨2606054343305303165518541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737369562203535443679027 2606054343305303165518541)
              ·
                refine ⟨977270378739488687069453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2606054343305303165518541 977270378739488687069453)
                ·
                  refine ⟨366476392027308257651045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977270378739488687069453 366476392027308257651045)
                  ·
                    rfl

theorem cell20_802924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_802924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802924 prefixEnd_802924 := by exact prefixLift 802924
  have htrace : WordTrace (prefixWord ++ tailWord_802924) baseStart_802924 baseEnd_802924 := by
    simpa [prefixWord, tailWord_802924, baseEnd_802924] using wordTrace_append hprefix tailTrace_802924
  have hstable : (prefixWord ++ tailWord_802924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802924).length < 2 ^ (prefixWord ++ tailWord_802924).sum := by decide
  have hdescent : baseEnd_802924 < baseStart_802924 := by decide
  rcases family_descends (prefixWord ++ tailWord_802924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802948 : List Nat := [2, 3, 2, 1, 2, 1, 2, 5, 2]
def baseStart_802948 : Nat := 118140960795 + 802948 * 2 ^ 59
def prefixEnd_802948 : Nat := 4983230072969 + 3 ^ 40 * 802948 * 2
def baseEnd_802948 : Nat := 366487346281270840850947

theorem tailTrace_802948 : CollatzResearch.WordTrace tailWord_802948 prefixEnd_802948 366487346281270840850947 := by
  unfold tailWord_802948
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642959747532001722912749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19523946330042668963883665 14642959747532001722912749)
  ·
    refine ⟨5491109905324500646092281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14642959747532001722912749 5491109905324500646092281)
    ·
      refine ⟨4118332428993375484569211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5491109905324500646092281 4118332428993375484569211)
      ·
        refine ⟨6177498643490063226853817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118332428993375484569211 6177498643490063226853817)
        ·
          refine ⟨4633123982617547420140363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6177498643490063226853817 4633123982617547420140363)
          ·
            refine ⟨6949685973926321130210545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633123982617547420140363 6949685973926321130210545)
            ·
              refine ⟨5212264480444740847657909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6949685973926321130210545 5212264480444740847657909)
              ·
                refine ⟨488649795041694454467929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5212264480444740847657909 488649795041694454467929)
                ·
                  refine ⟨366487346281270840850947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488649795041694454467929 366487346281270840850947)
                  ·
                    rfl

theorem cell20_802948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_802948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802948 prefixEnd_802948 := by exact prefixLift 802948
  have htrace : WordTrace (prefixWord ++ tailWord_802948) baseStart_802948 baseEnd_802948 := by
    simpa [prefixWord, tailWord_802948, baseEnd_802948] using wordTrace_append hprefix tailTrace_802948
  have hstable : (prefixWord ++ tailWord_802948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802948).length < 2 ^ (prefixWord ++ tailWord_802948).sum := by decide
  have hdescent : baseEnd_802948 < baseStart_802948 := by decide
  rcases family_descends (prefixWord ++ tailWord_802948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802976 : List Nat := [2, 1, 1, 4, 2, 2, 3, 5]
def baseStart_802976 : Nat := 118140960795 + 802976 * 2 ^ 59
def prefixEnd_802976 : Nat := 4983230072969 + 3 ^ 40 * 802976 * 2
def baseEnd_802976 : Nat := 122166708748075729305833

theorem tailTrace_802976 : CollatzResearch.WordTrace tailWord_802976 prefixEnd_802976 122166708748075729305833 := by
  unfold tailWord_802976
  simp only [CollatzResearch.WordTrace]
  refine ⟨14643470369481282113922391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19524627159308376151896521 14643470369481282113922391)
  ·
    refine ⟨21965205554221923170883587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14643470369481282113922391 21965205554221923170883587)
    ·
      refine ⟨32947808331332884756325381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21965205554221923170883587 32947808331332884756325381)
      ·
        refine ⟨6177714062124915891811009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32947808331332884756325381 6177714062124915891811009)
        ·
          refine ⟨4633285546593686918858257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6177714062124915891811009 4633285546593686918858257)
          ·
            refine ⟨3474964159945265189143693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4633285546593686918858257 3474964159945265189143693)
            ·
              refine ⟨1303111559979474445928885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3474964159945265189143693 1303111559979474445928885)
              ·
                refine ⟨122166708748075729305833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1303111559979474445928885 122166708748075729305833)
                ·
                  rfl

theorem cell20_802976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_802976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_802976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_802976 prefixEnd_802976 := by exact prefixLift 802976
  have htrace : WordTrace (prefixWord ++ tailWord_802976) baseStart_802976 baseEnd_802976 := by
    simpa [prefixWord, tailWord_802976, baseEnd_802976] using wordTrace_append hprefix tailTrace_802976
  have hstable : (prefixWord ++ tailWord_802976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802976).length < 2 ^ (prefixWord ++ tailWord_802976).sum := by decide
  have hdescent : baseEnd_802976 < baseStart_802976 := by decide
  rcases family_descends (prefixWord ++ tailWord_802976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803010 : List Nat := [3, 5, 1, 1, 1, 2, 7]
def baseStart_803010 : Nat := 118140960795 + 803010 * 2 ^ 59
def prefixEnd_803010 : Nat := 4983230072969 + 3 ^ 40 * 803010 * 2
def baseEnd_803010 : Nat := 40723960530074908976003

theorem tailTrace_803010 : CollatzResearch.WordTrace tailWord_803010 prefixEnd_803010 40723960530074908976003 := by
  unfold tailWord_803010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322045205209847008645621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19525453880559592023054989 7322045205209847008645621)
  ·
    refine ⟨686441737988423157060527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7322045205209847008645621 686441737988423157060527)
    ·
      refine ⟨1029662606982634735590791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 686441737988423157060527 1029662606982634735590791)
      ·
        refine ⟨1544493910473952103386187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029662606982634735590791 1544493910473952103386187)
        ·
          refine ⟨2316740865710928155079281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544493910473952103386187 2316740865710928155079281)
          ·
            refine ⟨1737555649283196116309461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2316740865710928155079281 1737555649283196116309461)
            ·
              refine ⟨40723960530074908976003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1737555649283196116309461 40723960530074908976003)
              ·
                rfl

theorem cell20_803010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 7].length) (baseStart_803010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803010 prefixEnd_803010 := by exact prefixLift 803010
  have htrace : WordTrace (prefixWord ++ tailWord_803010) baseStart_803010 baseEnd_803010 := by
    simpa [prefixWord, tailWord_803010, baseEnd_803010] using wordTrace_append hprefix tailTrace_803010
  have hstable : (prefixWord ++ tailWord_803010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803010).length < 2 ^ (prefixWord ++ tailWord_803010).sum := by decide
  have hdescent : baseEnd_803010 < baseStart_803010 := by decide
  rcases family_descends (prefixWord ++ tailWord_803010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803045 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_803045 : Nat := 118140960795 + 803045 * 2 ^ 59
def prefixEnd_803045 : Nat := 4983230072969 + 3 ^ 40 * 803045 * 2
def baseEnd_803045 : Nat := 366531619724369614617217

theorem tailTrace_803045 : CollatzResearch.WordTrace tailWord_803045 prefixEnd_803045 366531619724369614617217 := by
  unfold tailWord_803045
  simp only [CollatzResearch.WordTrace]
  refine ⟨29289457375712589012106589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19526304917141726008071059 29289457375712589012106589)
  ·
    refine ⟨10983546515892220879539971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29289457375712589012106589 10983546515892220879539971)
    ·
      refine ⟨16475319773838331319309957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10983546515892220879539971 16475319773838331319309957)
      ·
        refine ⟨3089122457594687122370617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16475319773838331319309957 3089122457594687122370617)
        ·
          refine ⟨2316841843196015341777963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3089122457594687122370617 2316841843196015341777963)
          ·
            refine ⟨3475262764794023012666945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316841843196015341777963 3475262764794023012666945)
            ·
              refine ⟨2606447073595517259500209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475262764794023012666945 2606447073595517259500209)
              ·
                refine ⟨1954835305196637944625157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606447073595517259500209 1954835305196637944625157)
                ·
                  refine ⟨366531619724369614617217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954835305196637944625157 366531619724369614617217)
                  ·
                    rfl

theorem cell20_803045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_803045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803045 prefixEnd_803045 := by exact prefixLift 803045
  have htrace : WordTrace (prefixWord ++ tailWord_803045) baseStart_803045 baseEnd_803045 := by
    simpa [prefixWord, tailWord_803045, baseEnd_803045] using wordTrace_append hprefix tailTrace_803045
  have hstable : (prefixWord ++ tailWord_803045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803045).length < 2 ^ (prefixWord ++ tailWord_803045).sum := by decide
  have hdescent : baseEnd_803045 < baseStart_803045 := by decide
  rcases family_descends (prefixWord ++ tailWord_803045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803079 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 4]
def baseStart_803079 : Nat := 118140960795 + 803079 * 2 ^ 59
def prefixEnd_803079 : Nat := 4983230072969 + 3 ^ 40 * 803079 * 2
def baseEnd_803079 : Nat := 366547138250816607483745

theorem tailTrace_803079 : CollatzResearch.WordTrace tailWord_803079 prefixEnd_803079 366547138250816607483745 := by
  unfold tailWord_803079
  simp only [CollatzResearch.WordTrace]
  refine ⟨29290697457589412818844291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19527131638392941879229527 29290697457589412818844291)
  ·
    refine ⟨43936046186384119228266437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29290697457589412818844291 43936046186384119228266437)
    ·
      refine ⟨8238008659947022355299957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43936046186384119228266437 8238008659947022355299957)
      ·
        refine ⟨772313311870033345809371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8238008659947022355299957 772313311870033345809371)
        ·
          refine ⟨1158469967805050018714057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772313311870033345809371 1158469967805050018714057)
          ·
            refine ⟨868852475853787514035543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1158469967805050018714057 868852475853787514035543)
            ·
              refine ⟨1303278713780681271053315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868852475853787514035543 1303278713780681271053315)
              ·
                refine ⟨1954918070671021906579973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303278713780681271053315 1954918070671021906579973)
                ·
                  refine ⟨366547138250816607483745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954918070671021906579973 366547138250816607483745)
                  ·
                    rfl

theorem cell20_803079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_803079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803079 prefixEnd_803079 := by exact prefixLift 803079
  have htrace : WordTrace (prefixWord ++ tailWord_803079) baseStart_803079 baseEnd_803079 := by
    simpa [prefixWord, tailWord_803079, baseEnd_803079] using wordTrace_append hprefix tailTrace_803079
  have hstable : (prefixWord ++ tailWord_803079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803079).length < 2 ^ (prefixWord ++ tailWord_803079).sum := by decide
  have hdescent : baseEnd_803079 < baseStart_803079 := by decide
  rcases family_descends (prefixWord ++ tailWord_803079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803134 : List Nat := [4, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_803134 : Nat := 118140960795 + 803134 * 2 ^ 59
def prefixEnd_803134 : Nat := 4983230072969 + 3 ^ 40 * 803134 * 2
def baseEnd_803134 : Nat := 366572241749480860650187

theorem tailTrace_803134 : CollatzResearch.WordTrace tailWord_803134 prefixEnd_803134 366572241749480860650187 := by
  unfold tailWord_803134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661587934048769651512057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19528468981593438141397637 3661587934048769651512057)
  ·
    refine ⟨2746190950536577238634043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3661587934048769651512057 2746190950536577238634043)
    ·
      refine ⟨4119286425804865857951065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746190950536577238634043 4119286425804865857951065)
      ·
        refine ⟨3089464819353649393463299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4119286425804865857951065 3089464819353649393463299)
        ·
          refine ⟨4634197229030474090194949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089464819353649393463299 4634197229030474090194949)
          ·
            refine ⟨868911980443213891911553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4634197229030474090194949 868911980443213891911553)
            ·
              refine ⟨651683985332410418933665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868911980443213891911553 651683985332410418933665)
              ·
                refine ⟨488762988999307814200249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651683985332410418933665 488762988999307814200249)
                ·
                  refine ⟨366572241749480860650187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488762988999307814200249 366572241749480860650187)
                  ·
                    rfl

theorem cell20_803134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_803134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803134 prefixEnd_803134 := by exact prefixLift 803134
  have htrace : WordTrace (prefixWord ++ tailWord_803134) baseStart_803134 baseEnd_803134 := by
    simpa [prefixWord, tailWord_803134, baseEnd_803134] using wordTrace_append hprefix tailTrace_803134
  have hstable : (prefixWord ++ tailWord_803134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803134).length < 2 ^ (prefixWord ++ tailWord_803134).sum := by decide
  have hdescent : baseEnd_803134 < baseStart_803134 := by decide
  rcases family_descends (prefixWord ++ tailWord_803134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803176 : List Nat := [2, 1, 4, 2, 2, 1, 1, 5, 2]
def baseStart_803176 : Nat := 118140960795 + 803176 * 2 ^ 59
def prefixEnd_803176 : Nat := 4983230072969 + 3 ^ 40 * 803176 * 2
def baseEnd_803176 : Nat := 366591411693915381250015

theorem tailTrace_803176 : CollatzResearch.WordTrace tailWord_803176 prefixEnd_803176 366591411693915381250015 := by
  unfold tailWord_803176
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647117669118999192562691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19529490225491998923416921 14647117669118999192562691)
  ·
    refine ⟨21970676503678498788844037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14647117669118999192562691 21970676503678498788844037)
    ·
      refine ⟨4119501844439718522908257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21970676503678498788844037 4119501844439718522908257)
      ·
        refine ⟨3089626383329788892181193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4119501844439718522908257 3089626383329788892181193)
        ·
          refine ⟨2317219787497341669135895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3089626383329788892181193 2317219787497341669135895)
          ·
            refine ⟨3475829681246012503703843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317219787497341669135895 3475829681246012503703843)
            ·
              refine ⟨5213744521869018755555765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475829681246012503703843 5213744521869018755555765)
              ·
                refine ⟨488788548925220508333353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5213744521869018755555765 488788548925220508333353)
                ·
                  refine ⟨366591411693915381250015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488788548925220508333353 366591411693915381250015)
                  ·
                    rfl

theorem cell20_803176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_803176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803176 prefixEnd_803176 := by exact prefixLift 803176
  have htrace : WordTrace (prefixWord ++ tailWord_803176) baseStart_803176 baseEnd_803176 := by
    simpa [prefixWord, tailWord_803176, baseEnd_803176] using wordTrace_append hprefix tailTrace_803176
  have hstable : (prefixWord ++ tailWord_803176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803176).length < 2 ^ (prefixWord ++ tailWord_803176).sum := by decide
  have hdescent : baseEnd_803176 < baseStart_803176 := by decide
  rcases family_descends (prefixWord ++ tailWord_803176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803197 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_803197 : Nat := 118140960795 + 803197 * 2 ^ 59
def prefixEnd_803197 : Nat := 4983230072969 + 3 ^ 40 * 803197 * 2
def baseEnd_803197 : Nat := 366600996666132641549929

theorem tailTrace_803197 : CollatzResearch.WordTrace tailWord_803197 prefixEnd_803197 366600996666132641549929 := by
  unfold tailWord_803197
  simp only [CollatzResearch.WordTrace]
  refine ⟨29295001271161918971639845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19530000847441279314426563 29295001271161918971639845)
  ·
    refine ⟨5492812738342859807182471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29295001271161918971639845 5492812738342859807182471)
    ·
      refine ⟨8239219107514289710773707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492812738342859807182471 8239219107514289710773707)
      ·
        refine ⟨12358828661271434566160561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239219107514289710773707 12358828661271434566160561)
        ·
          refine ⟨9269121495953575924620421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12358828661271434566160561 9269121495953575924620421)
          ·
            refine ⟨1737960280491295485866329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9269121495953575924620421 1737960280491295485866329)
            ·
              refine ⟨1303470210368471614399747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737960280491295485866329 1303470210368471614399747)
              ·
                refine ⟨1955205315552707421599621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303470210368471614399747 1955205315552707421599621)
                ·
                  refine ⟨366600996666132641549929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1955205315552707421599621 366600996666132641549929)
                  ·
                    rfl

theorem cell20_803197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_803197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803197 prefixEnd_803197 := by exact prefixLift 803197
  have htrace : WordTrace (prefixWord ++ tailWord_803197) baseStart_803197 baseEnd_803197 := by
    simpa [prefixWord, tailWord_803197, baseEnd_803197] using wordTrace_append hprefix tailTrace_803197
  have hstable : (prefixWord ++ tailWord_803197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803197).length < 2 ^ (prefixWord ++ tailWord_803197).sum := by decide
  have hdescent : baseEnd_803197 < baseStart_803197 := by decide
  rcases family_descends (prefixWord ++ tailWord_803197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803225 : List Nat := [1, 2, 1, 2, 1, 4, 3, 6]
def baseStart_803225 : Nat := 118140960795 + 803225 * 2 ^ 59
def prefixEnd_803225 : Nat := 4983230072969 + 3 ^ 40 * 803225 * 2
def baseEnd_803225 : Nat := 122204592209696329538827

theorem tailTrace_803225 : CollatzResearch.WordTrace tailWord_803225 prefixEnd_803225 122204592209696329538827 := by
  unfold tailWord_803225
  simp only [CollatzResearch.WordTrace]
  refine ⟨29296022515060479753659129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19530681676706986502439419 29296022515060479753659129)
  ·
    refine ⟨21972016886295359815244347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29296022515060479753659129 21972016886295359815244347)
    ·
      refine ⟨32958025329443039722866521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21972016886295359815244347 32958025329443039722866521)
      ·
        refine ⟨24718518997082279792149891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32958025329443039722866521 24718518997082279792149891)
        ·
          refine ⟨37077778495623419688224837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24718518997082279792149891 37077778495623419688224837)
          ·
            refine ⟨6952083467929391191542157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37077778495623419688224837 6952083467929391191542157)
            ·
              refine ⟨2607031300473521696828309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6952083467929391191542157 2607031300473521696828309)
              ·
                refine ⟨122204592209696329538827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2607031300473521696828309 122204592209696329538827)
                ·
                  rfl

theorem cell20_803225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_803225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803225 prefixEnd_803225 := by exact prefixLift 803225
  have htrace : WordTrace (prefixWord ++ tailWord_803225) baseStart_803225 baseEnd_803225 := by
    simpa [prefixWord, tailWord_803225, baseEnd_803225] using wordTrace_append hprefix tailTrace_803225
  have hstable : (prefixWord ++ tailWord_803225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803225).length < 2 ^ (prefixWord ++ tailWord_803225).sum := by decide
  have hdescent : baseEnd_803225 < baseStart_803225 := by decide
  rcases family_descends (prefixWord ++ tailWord_803225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803249 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_803249 : Nat := 118140960795 + 803249 * 2 ^ 59
def prefixEnd_803249 : Nat := 4983230072969 + 3 ^ 40 * 803249 * 2
def baseEnd_803249 : Nat := 366624730883051571816383

theorem tailTrace_803249 : CollatzResearch.WordTrace tailWord_803249 prefixEnd_803249 366624730883051571816383 := by
  unfold tailWord_803249
  simp only [CollatzResearch.WordTrace]
  refine ⟨29296897866973531852532801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19531265244649021235021867 29296897866973531852532801)
  ·
    refine ⟨21972673400230148889399601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29296897866973531852532801 21972673400230148889399601)
    ·
      refine ⟨16479505050172611667049701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21972673400230148889399601 16479505050172611667049701)
      ·
        refine ⟨3089907196907364687571819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16479505050172611667049701 3089907196907364687571819)
        ·
          refine ⟨4634860795361047031357729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089907196907364687571819 4634860795361047031357729)
          ·
            refine ⟨3476145596520785273518297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4634860795361047031357729 3476145596520785273518297)
            ·
              refine ⟨2607109197390588955138723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476145596520785273518297 2607109197390588955138723)
              ·
                refine ⟨3910663796085883432708085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607109197390588955138723 3910663796085883432708085)
                ·
                  refine ⟨366624730883051571816383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3910663796085883432708085 366624730883051571816383)
                  ·
                    rfl

theorem cell20_803249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_803249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803249 prefixEnd_803249 := by exact prefixLift 803249
  have htrace : WordTrace (prefixWord ++ tailWord_803249) baseStart_803249 baseEnd_803249 := by
    simpa [prefixWord, tailWord_803249, baseEnd_803249] using wordTrace_append hprefix tailTrace_803249
  have hstable : (prefixWord ++ tailWord_803249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803249).length < 2 ^ (prefixWord ++ tailWord_803249).sum := by decide
  have hdescent : baseEnd_803249 < baseStart_803249 := by decide
  rcases family_descends (prefixWord ++ tailWord_803249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803301 : List Nat := [1, 3, 1, 5, 10]
def baseStart_803301 : Nat := 118140960795 + 803301 * 2 ^ 59
def prefixEnd_803301 : Nat := 4983230072969 + 3 ^ 40 * 803301 * 2
def baseEnd_803301 : Nat := 4526524260493462988677

theorem tailTrace_803301 : CollatzResearch.WordTrace tailWord_803301 prefixEnd_803301 4526524260493462988677 := by
  unfold tailWord_803301
  simp only [CollatzResearch.WordTrace]
  refine ⟨29298794462785144733425757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19532529641856763155617171 29298794462785144733425757)
  ·
    refine ⟨10987047923544429275034659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29298794462785144733425757 10987047923544429275034659)
    ·
      refine ⟨16480571885316643912551989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10987047923544429275034659 16480571885316643912551989)
      ·
        refine ⟨1545053614248435366801749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16480571885316643912551989 1545053614248435366801749)
        ·
          refine ⟨4526524260493462988677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1545053614248435366801749 4526524260493462988677)
          ·
            rfl

theorem cell20_803301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 10].length) (baseStart_803301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803301 prefixEnd_803301 := by exact prefixLift 803301
  have htrace : WordTrace (prefixWord ++ tailWord_803301) baseStart_803301 baseEnd_803301 := by
    simpa [prefixWord, tailWord_803301, baseEnd_803301] using wordTrace_append hprefix tailTrace_803301
  have hstable : (prefixWord ++ tailWord_803301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803301).length < 2 ^ (prefixWord ++ tailWord_803301).sum := by decide
  have hdescent : baseEnd_803301 < baseStart_803301 := by decide
  rcases family_descends (prefixWord ++ tailWord_803301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803304 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_803304 : Nat := 118140960795 + 803304 * 2 ^ 59
def prefixEnd_803304 : Nat := 4983230072969 + 3 ^ 40 * 803304 * 2
def baseEnd_803304 : Nat := 366649834381715824982825

theorem tailTrace_803304 : CollatzResearch.WordTrace tailWord_803304 prefixEnd_803304 366649834381715824982825 := by
  unfold tailWord_803304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14649451940887138122892483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19532602587849517497189977 14649451940887138122892483)
  ·
    refine ⟨21974177911330707184338725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14649451940887138122892483 21974177911330707184338725)
    ·
      refine ⟨4120158358374507597063511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21974177911330707184338725 4120158358374507597063511)
      ·
        refine ⟨6180237537561761395595267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120158358374507597063511 6180237537561761395595267)
        ·
          refine ⟨9270356306342642093392901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6180237537561761395595267 9270356306342642093392901)
          ·
            refine ⟨1738191807439245392511169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9270356306342642093392901 1738191807439245392511169)
            ·
              refine ⟨1303643855579434044383377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738191807439245392511169 1303643855579434044383377)
              ·
                refine ⟨977732891684575533287533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1303643855579434044383377 977732891684575533287533)
                ·
                  refine ⟨366649834381715824982825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977732891684575533287533 366649834381715824982825)
                  ·
                    rfl

theorem cell20_803304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_803304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803304 prefixEnd_803304 := by exact prefixLift 803304
  have htrace : WordTrace (prefixWord ++ tailWord_803304) baseStart_803304 baseEnd_803304 := by
    simpa [prefixWord, tailWord_803304, baseEnd_803304] using wordTrace_append hprefix tailTrace_803304
  have hstable : (prefixWord ++ tailWord_803304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803304).length < 2 ^ (prefixWord ++ tailWord_803304).sum := by decide
  have hdescent : baseEnd_803304 < baseStart_803304 := by decide
  rcases family_descends (prefixWord ++ tailWord_803304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803314 : List Nat := [3, 2, 1, 4, 3, 1, 1, 5]
def baseStart_803314 : Nat := 118140960795 + 803314 * 2 ^ 59
def prefixEnd_803314 : Nat := 4983230072969 + 3 ^ 40 * 803314 * 2
def baseEnd_803314 : Nat := 122218132884733411549817

theorem tailTrace_803314 : CollatzResearch.WordTrace tailWord_803314 prefixEnd_803314 122218132884733411549817 := by
  unfold tailWord_803314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7324817152934511988412249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19532845741158698635765997 7324817152934511988412249)
  ·
    refine ⟨5493612864700883991309187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7324817152934511988412249 5493612864700883991309187)
    ·
      refine ⟨8240419297051325986963781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493612864700883991309187 8240419297051325986963781)
      ·
        refine ⟨1545078618197123622555709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8240419297051325986963781 1545078618197123622555709)
        ·
          refine ⟨579404481823921358458391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1545078618197123622555709 579404481823921358458391)
          ·
            refine ⟨869106722735882037687587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579404481823921358458391 869106722735882037687587)
            ·
              refine ⟨1303660084103823056531381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869106722735882037687587 1303660084103823056531381)
              ·
                refine ⟨122218132884733411549817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1303660084103823056531381 122218132884733411549817)
                ·
                  rfl

theorem cell20_803314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_803314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803314 prefixEnd_803314 := by exact prefixLift 803314
  have htrace : WordTrace (prefixWord ++ tailWord_803314) baseStart_803314 baseEnd_803314 := by
    simpa [prefixWord, tailWord_803314, baseEnd_803314] using wordTrace_append hprefix tailTrace_803314
  have hstable : (prefixWord ++ tailWord_803314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803314).length < 2 ^ (prefixWord ++ tailWord_803314).sum := by decide
  have hdescent : baseEnd_803314 < baseStart_803314 := by decide
  rcases family_descends (prefixWord ++ tailWord_803314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803325 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 3]
def baseStart_803325 : Nat := 118140960795 + 803325 * 2 ^ 59
def prefixEnd_803325 : Nat := 4983230072969 + 3 ^ 40 * 803325 * 2
def baseEnd_803325 : Nat := 366659419353933085282739

theorem tailTrace_803325 : CollatzResearch.WordTrace tailWord_803325 prefixEnd_803325 366659419353933085282739 := by
  unfold tailWord_803325
  simp only [CollatzResearch.WordTrace]
  refine ⟨29299669814698196832299429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19533113209798797888199619 29299669814698196832299429)
  ·
    refine ⟨5493688090255911906056143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29299669814698196832299429 5493688090255911906056143)
    ·
      refine ⟨8240532135383867859084215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493688090255911906056143 8240532135383867859084215)
      ·
        refine ⟨12360798203075801788626323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8240532135383867859084215 12360798203075801788626323)
        ·
          refine ⟨18541197304613702682939485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12360798203075801788626323 18541197304613702682939485)
          ·
            refine ⟨6952948989230138506102307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18541197304613702682939485 6952948989230138506102307)
            ·
              refine ⟨10429423483845207759153461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952948989230138506102307 10429423483845207759153461)
              ·
                refine ⟨977758451610488227420637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10429423483845207759153461 977758451610488227420637)
                ·
                  refine ⟨366659419353933085282739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977758451610488227420637 366659419353933085282739)
                  ·
                    rfl

theorem cell20_803325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_803325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803325 prefixEnd_803325 := by exact prefixLift 803325
  have htrace : WordTrace (prefixWord ++ tailWord_803325) baseStart_803325 baseEnd_803325 := by
    simpa [prefixWord, tailWord_803325, baseEnd_803325] using wordTrace_append hprefix tailTrace_803325
  have hstable : (prefixWord ++ tailWord_803325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803325).length < 2 ^ (prefixWord ++ tailWord_803325).sum := by decide
  have hdescent : baseEnd_803325 < baseStart_803325 := by decide
  rcases family_descends (prefixWord ++ tailWord_803325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803335 : List Nat := [1, 1, 4, 3, 3, 1, 3, 4]
def baseStart_803335 : Nat := 118140960795 + 803335 * 2 ^ 59
def prefixEnd_803335 : Nat := 4983230072969 + 3 ^ 40 * 803335 * 2
def baseEnd_803335 : Nat := 122221327875472498316455

theorem tailTrace_803335 : CollatzResearch.WordTrace tailWord_803335 prefixEnd_803335 122221327875472498316455 := by
  unfold tailWord_803335
  simp only [CollatzResearch.WordTrace]
  refine ⟨29300034544661968540163459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19533356363107979026775639 29300034544661968540163459)
  ·
    refine ⟨43950051816992952810245189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29300034544661968540163459 43950051816992952810245189)
    ·
      refine ⟨8240634715686178651920973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43950051816992952810245189 8240634715686178651920973)
      ·
        refine ⟨3090238018382316994470365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8240634715686178651920973 3090238018382316994470365)
        ·
          refine ⟨1158839256893368872926387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3090238018382316994470365 1158839256893368872926387)
          ·
            refine ⟨1738258885340053309389581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158839256893368872926387 1738258885340053309389581)
            ·
              refine ⟨651847082002519991021093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1738258885340053309389581 651847082002519991021093)
              ·
                refine ⟨122221327875472498316455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651847082002519991021093 122221327875472498316455)
                ·
                  rfl

theorem cell20_803335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_803335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803335 prefixEnd_803335 := by exact prefixLift 803335
  have htrace : WordTrace (prefixWord ++ tailWord_803335) baseStart_803335 baseEnd_803335 := by
    simpa [prefixWord, tailWord_803335, baseEnd_803335] using wordTrace_append hprefix tailTrace_803335
  have hstable : (prefixWord ++ tailWord_803335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803335).length < 2 ^ (prefixWord ++ tailWord_803335).sum := by decide
  have hdescent : baseEnd_803335 < baseStart_803335 := by decide
  rcases family_descends (prefixWord ++ tailWord_803335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803363 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_803363 : Nat := 118140960795 + 803363 * 2 ^ 59
def prefixEnd_803363 : Nat := 4983230072969 + 3 ^ 40 * 803363 * 2
def baseEnd_803363 : Nat := 366676763589373842015917

theorem tailTrace_803363 : CollatzResearch.WordTrace tailWord_803363 prefixEnd_803363 366676763589373842015917 := by
  unfold tailWord_803363
  simp only [CollatzResearch.WordTrace]
  refine ⟨29301055788560529322182743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19534037192373686214788495 29301055788560529322182743)
  ·
    refine ⟨43951583682840793983274115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29301055788560529322182743 43951583682840793983274115)
    ·
      refine ⟨65927375524261190974911173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43951583682840793983274115 65927375524261190974911173)
      ·
        refine ⟨12361382910798973307795845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65927375524261190974911173 12361382910798973307795845)
        ·
          refine ⟨2317759295774807495211721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12361382910798973307795845 2317759295774807495211721)
          ·
            refine ⟨1738319471831105621408791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2317759295774807495211721 1738319471831105621408791)
            ·
              refine ⟨2607479207746658432113187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738319471831105621408791 2607479207746658432113187)
              ·
                refine ⟨3911218811619987648169781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607479207746658432113187 3911218811619987648169781)
                ·
                  refine ⟨366676763589373842015917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3911218811619987648169781 366676763589373842015917)
                  ·
                    rfl

theorem cell20_803363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_803363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803363 prefixEnd_803363 := by exact prefixLift 803363
  have htrace : WordTrace (prefixWord ++ tailWord_803363) baseStart_803363 baseEnd_803363 := by
    simpa [prefixWord, tailWord_803363, baseEnd_803363] using wordTrace_append hprefix tailTrace_803363
  have hstable : (prefixWord ++ tailWord_803363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803363).length < 2 ^ (prefixWord ++ tailWord_803363).sum := by decide
  have hdescent : baseEnd_803363 < baseStart_803363 := by decide
  rcases family_descends (prefixWord ++ tailWord_803363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803396 : List Nat := [2, 3, 5, 1, 2, 1, 1, 3, 2]
def baseStart_803396 : Nat := 118140960795 + 803396 * 2 ^ 59
def prefixEnd_803396 : Nat := 4983230072969 + 3 ^ 40 * 803396 * 2
def baseEnd_803396 : Nat := 366691825688572393915783

theorem tailTrace_803396 : CollatzResearch.WordTrace tailWord_803396 prefixEnd_803396 366691825688572393915783 := by
  unfold tailWord_803396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14651129698720487979067021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19534839598293983972089361 14651129698720487979067021)
  ·
    refine ⟨5494173637020182992150133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14651129698720487979067021 5494173637020182992150133)
    ·
      refine ⟨515078778470642155514075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5494173637020182992150133 515078778470642155514075)
      ·
        refine ⟨772618167705963233271113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515078778470642155514075 772618167705963233271113)
        ·
          refine ⟨579463625779472424953335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772618167705963233271113 579463625779472424953335)
          ·
            refine ⟨869195438669208637430003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579463625779472424953335 869195438669208637430003)
            ·
              refine ⟨1303793158003812956145005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869195438669208637430003 1303793158003812956145005)
              ·
                refine ⟨488922434251429858554377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1303793158003812956145005 488922434251429858554377)
                ·
                  refine ⟨366691825688572393915783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488922434251429858554377 366691825688572393915783)
                  ·
                    rfl

theorem cell20_803396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_803396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803396 prefixEnd_803396 := by exact prefixLift 803396
  have htrace : WordTrace (prefixWord ++ tailWord_803396) baseStart_803396 baseEnd_803396 := by
    simpa [prefixWord, tailWord_803396, baseEnd_803396] using wordTrace_append hprefix tailTrace_803396
  have hstable : (prefixWord ++ tailWord_803396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803396).length < 2 ^ (prefixWord ++ tailWord_803396).sum := by decide
  have hdescent : baseEnd_803396 < baseStart_803396 := by decide
  rcases family_descends (prefixWord ++ tailWord_803396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803425 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 4]
def baseStart_803425 : Nat := 118140960795 + 803425 * 2 ^ 59
def prefixEnd_803425 : Nat := 4983230072969 + 3 ^ 40 * 803425 * 2
def baseEnd_803425 : Nat := 366705062078777181948997

theorem tailTrace_803425 : CollatzResearch.WordTrace tailWord_803425 prefixEnd_803425 366705062078777181948997 := by
  unfold tailWord_803425
  simp only [CollatzResearch.WordTrace]
  refine ⟨29303317114335913910939729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19535544742890609273959819 29303317114335913910939729)
  ·
    refine ⟨21977487835751935433204797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29303317114335913910939729 21977487835751935433204797)
    ·
      refine ⟨8241557938406975787451799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21977487835751935433204797 8241557938406975787451799)
      ·
        refine ⟨12362336907610463681177699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8241557938406975787451799 12362336907610463681177699)
        ·
          refine ⟨18543505361415695521766549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12362336907610463681177699 18543505361415695521766549)
          ·
            refine ⟨869226813816360727582807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18543505361415695521766549 869226813816360727582807)
            ·
              refine ⟨1303840220724541091374211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869226813816360727582807 1303840220724541091374211)
              ·
                refine ⟨1955760331086811637061317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303840220724541091374211 1955760331086811637061317)
                ·
                  refine ⟨366705062078777181948997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1955760331086811637061317 366705062078777181948997)
                  ·
                    rfl

theorem cell20_803425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_803425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803425 prefixEnd_803425 := by exact prefixLift 803425
  have htrace : WordTrace (prefixWord ++ tailWord_803425) baseStart_803425 baseEnd_803425 := by
    simpa [prefixWord, tailWord_803425, baseEnd_803425] using wordTrace_append hprefix tailTrace_803425
  have hstable : (prefixWord ++ tailWord_803425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803425).length < 2 ^ (prefixWord ++ tailWord_803425).sum := by decide
  have hdescent : baseEnd_803425 < baseStart_803425 := by decide
  rcases family_descends (prefixWord ++ tailWord_803425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803463 : List Nat := [1, 1, 4, 2, 1, 2, 2, 5, 2]
def baseStart_803463 : Nat := 118140960795 + 803463 * 2 ^ 59
def prefixEnd_803463 : Nat := 4983230072969 + 3 ^ 40 * 803463 * 2
def baseEnd_803463 : Nat := 366722406314217938682175

theorem tailTrace_803463 : CollatzResearch.WordTrace tailWord_803463 prefixEnd_803463 366722406314217938682175 := by
  unfold tailWord_803463
  simp only [CollatzResearch.WordTrace]
  refine ⟨29304703088198246400823043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19536468725465497600548695 29304703088198246400823043)
  ·
    refine ⟨43957054632297369601234565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29304703088198246400823043 43957054632297369601234565)
    ·
      refine ⟨8241947743555756800231481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43957054632297369601234565 8241947743555756800231481)
      ·
        refine ⟨6181460807666817600173611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8241947743555756800231481 6181460807666817600173611)
        ·
          refine ⟨9272191211500226400260417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6181460807666817600173611 9272191211500226400260417)
          ·
            refine ⟨6954143408625169800195313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9272191211500226400260417 6954143408625169800195313)
            ·
              refine ⟨5215607556468877350146485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6954143408625169800195313 5215607556468877350146485)
              ·
                refine ⟨488963208418957251576233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5215607556468877350146485 488963208418957251576233)
                ·
                  refine ⟨366722406314217938682175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488963208418957251576233 366722406314217938682175)
                  ·
                    rfl

theorem cell20_803463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 2].length) (baseStart_803463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803463 prefixEnd_803463 := by exact prefixLift 803463
  have htrace : WordTrace (prefixWord ++ tailWord_803463) baseStart_803463 baseEnd_803463 := by
    simpa [prefixWord, tailWord_803463, baseEnd_803463] using wordTrace_append hprefix tailTrace_803463
  have hstable : (prefixWord ++ tailWord_803463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803463).length < 2 ^ (prefixWord ++ tailWord_803463).sum := by decide
  have hdescent : baseEnd_803463 < baseStart_803463 := by decide
  rcases family_descends (prefixWord ++ tailWord_803463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803467 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_803467 : Nat := 118140960795 + 803467 * 2 ^ 59
def prefixEnd_803467 : Nat := 4983230072969 + 3 ^ 40 * 803467 * 2
def baseEnd_803467 : Nat := 366724232023211702548825

theorem tailTrace_803467 : CollatzResearch.WordTrace tailWord_803467 prefixEnd_803467 366724232023211702548825 := by
  unfold tailWord_803467
  simp only [CollatzResearch.WordTrace]
  refine ⟨29304848980183755083968655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19536565986789170055979103 29304848980183755083968655)
  ·
    refine ⟨43957273470275632625952983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29304848980183755083968655 43957273470275632625952983)
    ·
      refine ⟨65935910205413448938929475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43957273470275632625952983 65935910205413448938929475)
      ·
        refine ⟨98903865308120173408394213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65935910205413448938929475 98903865308120173408394213)
        ·
          refine ⟨18544474745272532514073915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98903865308120173408394213 18544474745272532514073915)
          ·
            refine ⟨27816712117908798771110873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18544474745272532514073915 27816712117908798771110873)
            ·
              refine ⟨20862534088431599078333155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27816712117908798771110873 20862534088431599078333155)
              ·
                refine ⟨31293801132647398617499733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20862534088431599078333155 31293801132647398617499733)
                ·
                  refine ⟨366724232023211702548825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31293801132647398617499733 366724232023211702548825)
                  ·
                    rfl

theorem cell20_803467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_803467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803467 prefixEnd_803467 := by exact prefixLift 803467
  have htrace : WordTrace (prefixWord ++ tailWord_803467) baseStart_803467 baseEnd_803467 := by
    simpa [prefixWord, tailWord_803467, baseEnd_803467] using wordTrace_append hprefix tailTrace_803467
  have hstable : (prefixWord ++ tailWord_803467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803467).length < 2 ^ (prefixWord ++ tailWord_803467).sum := by decide
  have hdescent : baseEnd_803467 < baseStart_803467 := by decide
  rcases family_descends (prefixWord ++ tailWord_803467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803476 : List Nat := [2, 4, 2, 2, 1, 3, 2, 2, 2]
def baseStart_803476 : Nat := 118140960795 + 803476 * 2 ^ 59
def prefixEnd_803476 : Nat := 4983230072969 + 3 ^ 40 * 803476 * 2
def baseEnd_803476 : Nat := 366728339868447671248789

theorem tailTrace_803476 : CollatzResearch.WordTrace tailWord_803476 prefixEnd_803476 366728339868447671248789 := by
  unfold tailWord_803476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14652588618575574810523141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19536784824767433080697521 14652588618575574810523141)
  ·
    refine ⟨2747360365982920276973089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14652588618575574810523141 2747360365982920276973089)
    ·
      refine ⟨2060520274487190207729817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2747360365982920276973089 2060520274487190207729817)
      ·
        refine ⟨1545390205865392655797363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2060520274487190207729817 1545390205865392655797363)
        ·
          refine ⟨2318085308798088983696045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545390205865392655797363 2318085308798088983696045)
          ·
            refine ⟨869281990799283368886017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2318085308798088983696045 869281990799283368886017)
            ·
              refine ⟨651961493099462526664513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869281990799283368886017 651961493099462526664513)
              ·
                refine ⟨488971119824596894998385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651961493099462526664513 488971119824596894998385)
                ·
                  refine ⟨366728339868447671248789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488971119824596894998385 366728339868447671248789)
                  ·
                    rfl

theorem cell20_803476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_803476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803476 prefixEnd_803476 := by exact prefixLift 803476
  have htrace : WordTrace (prefixWord ++ tailWord_803476) baseStart_803476 baseEnd_803476 := by
    simpa [prefixWord, tailWord_803476, baseEnd_803476] using wordTrace_append hprefix tailTrace_803476
  have hstable : (prefixWord ++ tailWord_803476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803476).length < 2 ^ (prefixWord ++ tailWord_803476).sum := by decide
  have hdescent : baseEnd_803476 < baseStart_803476 := by decide
  rcases family_descends (prefixWord ++ tailWord_803476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803501 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_803501 : Nat := 118140960795 + 803501 * 2 ^ 59
def prefixEnd_803501 : Nat := 4983230072969 + 3 ^ 40 * 803501 * 2
def baseEnd_803501 : Nat := 366739750549658695415353

theorem tailTrace_803501 : CollatzResearch.WordTrace tailWord_803501 prefixEnd_803501 366739750549658695415353 := by
  unfold tailWord_803501
  simp only [CollatzResearch.WordTrace]
  refine ⟨29306089062060578890706357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19537392708040385927137571 29306089062060578890706357)
  ·
    refine ⟨2747445849568179271003721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29306089062060578890706357 2747445849568179271003721)
    ·
      refine ⟨2060584387176134453252791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2747445849568179271003721 2060584387176134453252791)
      ·
        refine ⟨3090876580764201679879187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060584387176134453252791 3090876580764201679879187)
        ·
          refine ⟨4636314871146302519818781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090876580764201679879187 4636314871146302519818781)
          ·
            refine ⟨1738618076679863444932043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4636314871146302519818781 1738618076679863444932043)
            ·
              refine ⟨2607927115019795167398065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738618076679863444932043 2607927115019795167398065)
              ·
                refine ⟨1955945336264846375548549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607927115019795167398065 1955945336264846375548549)
                ·
                  refine ⟨366739750549658695415353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1955945336264846375548549 366739750549658695415353)
                  ·
                    rfl

theorem cell20_803501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_803501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803501 prefixEnd_803501 := by exact prefixLift 803501
  have htrace : WordTrace (prefixWord ++ tailWord_803501) baseStart_803501 baseEnd_803501 := by
    simpa [prefixWord, tailWord_803501, baseEnd_803501] using wordTrace_append hprefix tailTrace_803501
  have hstable : (prefixWord ++ tailWord_803501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803501).length < 2 ^ (prefixWord ++ tailWord_803501).sum := by decide
  have hdescent : baseEnd_803501 < baseStart_803501 := by decide
  rcases family_descends (prefixWord ++ tailWord_803501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803518 : List Nat := [4, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_803518 : Nat := 118140960795 + 803518 * 2 ^ 59
def prefixEnd_803518 : Nat := 4983230072969 + 3 ^ 40 * 803518 * 2
def baseEnd_803518 : Nat := 366747509812882191848617

theorem tailTrace_803518 : CollatzResearch.WordTrace tailWord_803518 prefixEnd_803518 366747509812882191848617 := by
  unfold tailWord_803518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663338637874873849259401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19537806068665993862716805 3663338637874873849259401)
  ·
    refine ⟨2747503978406155386944551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3663338637874873849259401 2747503978406155386944551)
    ·
      refine ⟨4121255967609233080416827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747503978406155386944551 4121255967609233080416827)
      ·
        refine ⟨6181883951413849620625241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121255967609233080416827 6181883951413849620625241)
        ·
          refine ⟨4636412963560387215468931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6181883951413849620625241 4636412963560387215468931)
          ·
            refine ⟨6954619445340580823203397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636412963560387215468931 6954619445340580823203397)
            ·
              refine ⟨1303991146001358904350637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6954619445340580823203397 1303991146001358904350637)
              ·
                refine ⟨488996679750509589131489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1303991146001358904350637 488996679750509589131489)
                ·
                  refine ⟨366747509812882191848617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488996679750509589131489 366747509812882191848617)
                  ·
                    rfl

theorem cell20_803518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_803518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803518 prefixEnd_803518 := by exact prefixLift 803518
  have htrace : WordTrace (prefixWord ++ tailWord_803518) baseStart_803518 baseEnd_803518 := by
    simpa [prefixWord, tailWord_803518, baseEnd_803518] using wordTrace_append hprefix tailTrace_803518
  have hstable : (prefixWord ++ tailWord_803518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803518).length < 2 ^ (prefixWord ++ tailWord_803518).sum := by decide
  have hdescent : baseEnd_803518 < baseStart_803518 := by decide
  rcases family_descends (prefixWord ++ tailWord_803518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803532 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_803532 : Nat := 118140960795 + 803532 * 2 ^ 59
def prefixEnd_803532 : Nat := 4983230072969 + 3 ^ 40 * 803532 * 2
def baseEnd_803532 : Nat := 366753899794360365381893

theorem tailTrace_803532 : CollatzResearch.WordTrace tailWord_803532 prefixEnd_803532 366753899794360365381893 := by
  unfold tailWord_803532
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653609862474135592542425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19538146483298847456723233 14653609862474135592542425)
  ·
    refine ⟨10990207396855601694406819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14653609862474135592542425 10990207396855601694406819)
    ·
      refine ⟨16485311095283402541610229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10990207396855601694406819 16485311095283402541610229)
      ·
        refine ⟨1545497915182818988275959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16485311095283402541610229 1545497915182818988275959)
        ·
          refine ⟨2318246872774228482413939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545497915182818988275959 2318246872774228482413939)
          ·
            refine ⟨3477370309161342723620909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318246872774228482413939 3477370309161342723620909)
            ·
              refine ⟨1304013865935503521357841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3477370309161342723620909 1304013865935503521357841)
              ·
                refine ⟨978010399451627641018381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304013865935503521357841 978010399451627641018381)
                ·
                  refine ⟨366753899794360365381893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978010399451627641018381 366753899794360365381893)
                  ·
                    rfl

theorem cell20_803532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_803532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803532 prefixEnd_803532 := by exact prefixLift 803532
  have htrace : WordTrace (prefixWord ++ tailWord_803532) baseStart_803532 baseEnd_803532 := by
    simpa [prefixWord, tailWord_803532, baseEnd_803532] using wordTrace_append hprefix tailTrace_803532
  have hstable : (prefixWord ++ tailWord_803532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803532).length < 2 ^ (prefixWord ++ tailWord_803532).sum := by decide
  have hdescent : baseEnd_803532 < baseStart_803532 := by decide
  rcases family_descends (prefixWord ++ tailWord_803532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803567 : List Nat := [1, 1, 2, 1, 5, 3, 1, 6]
def baseStart_803567 : Nat := 118140960795 + 803567 * 2 ^ 59
def prefixEnd_803567 : Nat := 4983230072969 + 3 ^ 40 * 803567 * 2
def baseEnd_803567 : Nat := 122256624916018599738361

theorem tailTrace_803567 : CollatzResearch.WordTrace tailWord_803567 prefixEnd_803567 122256624916018599738361 := by
  unfold tailWord_803567
  simp only [CollatzResearch.WordTrace]
  refine ⟨29308496279821472162608955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19538997519880981441739303 29308496279821472162608955)
  ·
    refine ⟨43962744419732208243913433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29308496279821472162608955 43962744419732208243913433)
    ·
      refine ⟨32972058314799156182935075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43962744419732208243913433 32972058314799156182935075)
      ·
        refine ⟨49458087472198734274402613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32972058314799156182935075 49458087472198734274402613)
        ·
          refine ⟨4636695700518631338225245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49458087472198734274402613 4636695700518631338225245)
          ·
            refine ⟨1738760887694486751834467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4636695700518631338225245 1738760887694486751834467)
            ·
              refine ⟨2608141331541730127751701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738760887694486751834467 2608141331541730127751701)
              ·
                refine ⟨122256624916018599738361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2608141331541730127751701 122256624916018599738361)
                ·
                  rfl

theorem cell20_803567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_803567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803567 prefixEnd_803567 := by exact prefixLift 803567
  have htrace : WordTrace (prefixWord ++ tailWord_803567) baseStart_803567 baseEnd_803567 := by
    simpa [prefixWord, tailWord_803567, baseEnd_803567] using wordTrace_append hprefix tailTrace_803567
  have hstable : (prefixWord ++ tailWord_803567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803567).length < 2 ^ (prefixWord ++ tailWord_803567).sum := by decide
  have hdescent : baseEnd_803567 < baseStart_803567 := by decide
  rcases family_descends (prefixWord ++ tailWord_803567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803591 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_803591 : Nat := 118140960795 + 803591 * 2 ^ 59
def prefixEnd_803591 : Nat := 4983230072969 + 3 ^ 40 * 803591 * 2
def baseEnd_803591 : Nat := 366780829002018382414985

theorem tailTrace_803591 : CollatzResearch.WordTrace tailWord_803591 prefixEnd_803591 366780829002018382414985 := by
  unfold tailWord_803591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29309371631734524261482627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19539581087823016174321751 29309371631734524261482627)
  ·
    refine ⟨43964057447601786392223941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29309371631734524261482627 43964057447601786392223941)
    ·
      refine ⟨8243260771425334948541989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43964057447601786392223941 8243260771425334948541989)
      ·
        refine ⟨1545611394642250302851623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8243260771425334948541989 1545611394642250302851623)
        ·
          refine ⟨2318417091963375454277435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545611394642250302851623 2318417091963375454277435)
          ·
            refine ⟨3477625637945063181416153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318417091963375454277435 3477625637945063181416153)
            ·
              refine ⟨2608219228458797386062115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3477625637945063181416153 2608219228458797386062115)
              ·
                refine ⟨3912328842688196079093173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608219228458797386062115 3912328842688196079093173)
                ·
                  refine ⟨366780829002018382414985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912328842688196079093173 366780829002018382414985)
                  ·
                    rfl

theorem cell20_803591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_803591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803591 prefixEnd_803591 := by exact prefixLift 803591
  have htrace : WordTrace (prefixWord ++ tailWord_803591) baseStart_803591 baseEnd_803591 := by
    simpa [prefixWord, tailWord_803591, baseEnd_803591] using wordTrace_append hprefix tailTrace_803591
  have hstable : (prefixWord ++ tailWord_803591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803591).length < 2 ^ (prefixWord ++ tailWord_803591).sum := by decide
  have hdescent : baseEnd_803591 < baseStart_803591 := by decide
  rcases family_descends (prefixWord ++ tailWord_803591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803594 : List Nat := [3, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_803594 : Nat := 118140960795 + 803594 * 2 ^ 59
def prefixEnd_803594 : Nat := 4983230072969 + 3 ^ 40 * 803594 * 2
def baseEnd_803594 : Nat := 366782198283763705314973

theorem tailTrace_803594 : CollatzResearch.WordTrace tailWord_803594 prefixEnd_803594 366782198283763705314973 := by
  unfold tailWord_803594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327370262680913943460459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19539654033815770515894557 7327370262680913943460459)
  ·
    refine ⟨10991055394021370915190689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7327370262680913943460459 10991055394021370915190689)
    ·
      refine ⟨8243291545516028186393017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10991055394021370915190689 8243291545516028186393017)
      ·
        refine ⟨6182468659137021139794763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8243291545516028186393017 6182468659137021139794763)
        ·
          refine ⟨9273702988705531709692145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182468659137021139794763 9273702988705531709692145)
          ·
            refine ⟨6955277241529148782269109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9273702988705531709692145 6955277241529148782269109)
            ·
              refine ⟨652057241393357698337729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6955277241529148782269109 652057241393357698337729)
              ·
                refine ⟨489042931045018273753297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652057241393357698337729 489042931045018273753297)
                ·
                  refine ⟨366782198283763705314973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489042931045018273753297 366782198283763705314973)
                  ·
                    rfl

theorem cell20_803594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_803594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803594 prefixEnd_803594 := by exact prefixLift 803594
  have htrace : WordTrace (prefixWord ++ tailWord_803594) baseStart_803594 baseEnd_803594 := by
    simpa [prefixWord, tailWord_803594, baseEnd_803594] using wordTrace_append hprefix tailTrace_803594
  have hstable : (prefixWord ++ tailWord_803594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803594).length < 2 ^ (prefixWord ++ tailWord_803594).sum := by decide
  have hdescent : baseEnd_803594 < baseStart_803594 := by decide
  rcases family_descends (prefixWord ++ tailWord_803594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803605 : List Nat := [1, 3, 2, 1, 2, 2, 4, 5]
def baseStart_803605 : Nat := 118140960795 + 803605 * 2 ^ 59
def prefixEnd_803605 : Nat := 4983230072969 + 3 ^ 40 * 803605 * 2
def baseEnd_803605 : Nat := 122262406327832185316087

theorem tailTrace_803605 : CollatzResearch.WordTrace tailWord_803605 prefixEnd_803605 122262406327832185316087 := by
  unfold tailWord_803605
  simp only [CollatzResearch.WordTrace]
  refine ⟨29309882253683804652492269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19539921502455869768328179 29309882253683804652492269)
  ·
    refine ⟨10991205845131426744684601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29309882253683804652492269 10991205845131426744684601)
    ·
      refine ⟨8243404383848570058513451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10991205845131426744684601 8243404383848570058513451)
      ·
        refine ⟨12365106575772855087770177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8243404383848570058513451 12365106575772855087770177)
        ·
          refine ⟨9273829931829641315827633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12365106575772855087770177 9273829931829641315827633)
          ·
            refine ⟨6955372448872230986870725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9273829931829641315827633 6955372448872230986870725)
            ·
              refine ⟨1304132334163543310038261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6955372448872230986870725 1304132334163543310038261)
              ·
                refine ⟨122262406327832185316087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1304132334163543310038261 122262406327832185316087)
                ·
                  rfl

theorem cell20_803605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_803605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803605 prefixEnd_803605 := by exact prefixLift 803605
  have htrace : WordTrace (prefixWord ++ tailWord_803605) baseStart_803605 baseEnd_803605 := by
    simpa [prefixWord, tailWord_803605, baseEnd_803605] using wordTrace_append hprefix tailTrace_803605
  have hstable : (prefixWord ++ tailWord_803605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803605).length < 2 ^ (prefixWord ++ tailWord_803605).sum := by decide
  have hdescent : baseEnd_803605 < baseStart_803605 := by decide
  rcases family_descends (prefixWord ++ tailWord_803605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803619 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_803619 : Nat := 118140960795 + 803619 * 2 ^ 59
def prefixEnd_803619 : Nat := 4983230072969 + 3 ^ 40 * 803619 * 2
def baseEnd_803619 : Nat := 366793608964974729481537

theorem tailTrace_803619 : CollatzResearch.WordTrace tailWord_803619 prefixEnd_803619 366793608964974729481537 := by
  unfold tailWord_803619
  simp only [CollatzResearch.WordTrace]
  refine ⟨29310392875633085043501911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19540261917088723362334607 29310392875633085043501911)
  ·
    refine ⟨43965589313449627565252867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29310392875633085043501911 43965589313449627565252867)
    ·
      refine ⟨65948383970174441347879301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43965589313449627565252867 65948383970174441347879301)
      ·
        refine ⟨12365321994407707752727369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65948383970174441347879301 12365321994407707752727369)
        ·
          refine ⟨9273991495805780814545527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12365321994407707752727369 9273991495805780814545527)
          ·
            refine ⟨13910987243708671221818291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9273991495805780814545527 13910987243708671221818291)
            ·
              refine ⟨20866480865563006832727437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13910987243708671221818291 20866480865563006832727437)
              ·
                refine ⟨7824930324586127562272789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20866480865563006832727437 7824930324586127562272789)
                ·
                  refine ⟨366793608964974729481537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7824930324586127562272789 366793608964974729481537)
                  ·
                    rfl

theorem cell20_803619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_803619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803619 prefixEnd_803619 := by exact prefixLift 803619
  have htrace : WordTrace (prefixWord ++ tailWord_803619) baseStart_803619 baseEnd_803619 := by
    simpa [prefixWord, tailWord_803619, baseEnd_803619] using wordTrace_append hprefix tailTrace_803619
  have hstable : (prefixWord ++ tailWord_803619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803619).length < 2 ^ (prefixWord ++ tailWord_803619).sum := by decide
  have hdescent : baseEnd_803619 < baseStart_803619 := by decide
  rcases family_descends (prefixWord ++ tailWord_803619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803649 : List Nat := [1, 2, 5, 3, 1, 1, 1, 4, 2]
def baseStart_803649 : Nat := 118140960795 + 803649 * 2 ^ 59
def prefixEnd_803649 : Nat := 4983230072969 + 3 ^ 40 * 803649 * 2
def baseEnd_803649 : Nat := 366807301782427958481415

theorem tailTrace_803649 : CollatzResearch.WordTrace tailWord_803649 prefixEnd_803649 366807301782427958481415 := by
  unfold tailWord_803649
  simp only [CollatzResearch.WordTrace]
  refine ⟨29311487065524400167094001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19540991377016266778062667 29311487065524400167094001)
  ·
    refine ⟨21983615299143300125320501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29311487065524400167094001 21983615299143300125320501)
    ·
      refine ⟨2060963934294684386748797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21983615299143300125320501 2060963934294684386748797)
      ·
        refine ⟨772861475360506645030799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2060963934294684386748797 772861475360506645030799)
        ·
          refine ⟨1159292213040759967546199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772861475360506645030799 1159292213040759967546199)
          ·
            refine ⟨1738938319561139951319299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159292213040759967546199 1738938319561139951319299)
            ·
              refine ⟨2608407479341709926978949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738938319561139951319299 2608407479341709926978949)
              ·
                refine ⟨489076402376570611308553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2608407479341709926978949 489076402376570611308553)
                ·
                  refine ⟨366807301782427958481415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489076402376570611308553 366807301782427958481415)
                  ·
                    rfl

theorem cell20_803649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_803649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803649 prefixEnd_803649 := by exact prefixLift 803649
  have htrace : WordTrace (prefixWord ++ tailWord_803649) baseStart_803649 baseEnd_803649 := by
    simpa [prefixWord, tailWord_803649, baseEnd_803649] using wordTrace_append hprefix tailTrace_803649
  have hstable : (prefixWord ++ tailWord_803649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803649).length < 2 ^ (prefixWord ++ tailWord_803649).sum := by decide
  have hdescent : baseEnd_803649 < baseStart_803649 := by decide
  rcases family_descends (prefixWord ++ tailWord_803649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803660 : List Nat := [2, 2, 1, 3, 3, 3, 1, 5]
def baseStart_803660 : Nat := 118140960795 + 803660 * 2 ^ 59
def prefixEnd_803660 : Nat := 4983230072969 + 3 ^ 40 * 803660 * 2
def baseEnd_803660 : Nat := 122270774160720269704901

theorem tailTrace_803660 : CollatzResearch.WordTrace tailWord_803660 prefixEnd_803660 122270774160720269704901 := by
  unfold tailWord_803660
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655944134242274522872217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19541258845656366030496289 14655944134242274522872217)
  ·
    refine ⟨10991958100681705892154163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14655944134242274522872217 10991958100681705892154163)
    ·
      refine ⟨16487937151022558838231245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10991958100681705892154163 16487937151022558838231245)
      ·
        refine ⟨6182976431633459564336717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16487937151022558838231245 6182976431633459564336717)
        ·
          refine ⟨2318616161862547336626269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6182976431633459564336717 2318616161862547336626269)
          ·
            refine ⟨869481060698455251234851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2318616161862547336626269 869481060698455251234851)
            ·
              refine ⟨1304221591047682876852277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869481060698455251234851 1304221591047682876852277)
              ·
                refine ⟨122270774160720269704901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1304221591047682876852277 122270774160720269704901)
                ·
                  rfl

theorem cell20_803660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_803660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803660 prefixEnd_803660 := by exact prefixLift 803660
  have htrace : WordTrace (prefixWord ++ tailWord_803660) baseStart_803660 baseEnd_803660 := by
    simpa [prefixWord, tailWord_803660, baseEnd_803660] using wordTrace_append hprefix tailTrace_803660
  have hstable : (prefixWord ++ tailWord_803660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803660).length < 2 ^ (prefixWord ++ tailWord_803660).sum := by decide
  have hdescent : baseEnd_803660 < baseStart_803660 := by decide
  rcases family_descends (prefixWord ++ tailWord_803660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803674 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_803674 : Nat := 118140960795 + 803674 * 2 ^ 59
def prefixEnd_803674 : Nat := 4983230072969 + 3 ^ 40 * 803674 * 2
def baseEnd_803674 : Nat := 366818712463638982647979

theorem tailTrace_803674 : CollatzResearch.WordTrace tailWord_803674 prefixEnd_803674 366818712463638982647979 := by
  unfold tailWord_803674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7328099722608457359188519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19541599260289219624502717 7328099722608457359188519)
  ·
    refine ⟨10992149583912686038782779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7328099722608457359188519 10992149583912686038782779)
    ·
      refine ⟨16488224375869029058174169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10992149583912686038782779 16488224375869029058174169)
      ·
        refine ⟨12366168281901771793630627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16488224375869029058174169 12366168281901771793630627)
        ·
          refine ⟨18549252422852657690445941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12366168281901771793630627 18549252422852657690445941)
          ·
            refine ⟨1738992414642436658479307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18549252422852657690445941 1738992414642436658479307)
            ·
              refine ⟨2608488621963654987718961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738992414642436658479307 2608488621963654987718961)
              ·
                refine ⟨1956366466472741240789221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608488621963654987718961 1956366466472741240789221)
                ·
                  refine ⟨366818712463638982647979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1956366466472741240789221 366818712463638982647979)
                  ·
                    rfl

theorem cell20_803674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_803674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803674 prefixEnd_803674 := by exact prefixLift 803674
  have htrace : WordTrace (prefixWord ++ tailWord_803674) baseStart_803674 baseEnd_803674 := by
    simpa [prefixWord, tailWord_803674, baseEnd_803674] using wordTrace_append hprefix tailTrace_803674
  have hstable : (prefixWord ++ tailWord_803674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803674).length < 2 ^ (prefixWord ++ tailWord_803674).sum := by decide
  have hdescent : baseEnd_803674 < baseStart_803674 := by decide
  rcases family_descends (prefixWord ++ tailWord_803674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803705 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 3]
def baseStart_803705 : Nat := 118140960795 + 803705 * 2 ^ 59
def prefixEnd_803705 : Nat := 4983230072969 + 3 ^ 40 * 803705 * 2
def baseEnd_803705 : Nat := 366832861708340652614519

theorem tailTrace_803705 : CollatzResearch.WordTrace tailWord_803705 prefixEnd_803705 366832861708340652614519 := by
  unfold tailWord_803705
  simp only [CollatzResearch.WordTrace]
  refine ⟨29313529553321521731132569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19542353035547681154088379 29313529553321521731132569)
  ·
    refine ⟨21985147164991141298349427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29313529553321521731132569 21985147164991141298349427)
    ·
      refine ⟨32977720747486711947524141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21985147164991141298349427 32977720747486711947524141)
      ·
        refine ⟨12366645280307516980321553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32977720747486711947524141 12366645280307516980321553)
        ·
          refine ⟨9274983960230637735241165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12366645280307516980321553 9274983960230637735241165)
          ·
            refine ⟨3478118985086489150715437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9274983960230637735241165 3478118985086489150715437)
            ·
              refine ⟨1304294619407433431518289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478118985086489150715437 1304294619407433431518289)
              ·
                refine ⟨978220964555575073638717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304294619407433431518289 978220964555575073638717)
                ·
                  refine ⟨366832861708340652614519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978220964555575073638717 366832861708340652614519)
                  ·
                    rfl

theorem cell20_803705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_803705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803705 prefixEnd_803705 := by exact prefixLift 803705
  have htrace : WordTrace (prefixWord ++ tailWord_803705) baseStart_803705 baseEnd_803705 := by
    simpa [prefixWord, tailWord_803705, baseEnd_803705] using wordTrace_append hprefix tailTrace_803705
  have hstable : (prefixWord ++ tailWord_803705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803705).length < 2 ^ (prefixWord ++ tailWord_803705).sum := by decide
  have hdescent : baseEnd_803705 < baseStart_803705 := by decide
  rcases family_descends (prefixWord ++ tailWord_803705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803746 : List Nat := [3, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_803746 : Nat := 118140960795 + 803746 * 2 ^ 59
def prefixEnd_803746 : Nat := 4983230072969 + 3 ^ 40 * 803746 * 2
def baseEnd_803746 : Nat := 366851575225526732247685

theorem tailTrace_803746 : CollatzResearch.WordTrace tailWord_803746 prefixEnd_803746 366851575225526732247685 := by
  unfold tailWord_803746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7328756236543246433343773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19543349964115323822250061 7328756236543246433343773)
  ·
    refine ⟨2748283588703717412503915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7328756236543246433343773 2748283588703717412503915)
    ·
      refine ⟨4122425383055576118755873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2748283588703717412503915 4122425383055576118755873)
      ·
        refine ⟨3091819037291682089066905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4122425383055576118755873 3091819037291682089066905)
        ·
          refine ⟨2318864277968761566800179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091819037291682089066905 2318864277968761566800179)
          ·
            refine ⟨3478296416953142350200269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318864277968761566800179 3478296416953142350200269)
            ·
              refine ⟨1304361156357428381325101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478296416953142350200269 1304361156357428381325101)
              ·
                refine ⟨489135433634035642996913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304361156357428381325101 489135433634035642996913)
                ·
                  refine ⟨366851575225526732247685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489135433634035642996913 366851575225526732247685)
                  ·
                    rfl

theorem cell20_803746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_803746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803746 prefixEnd_803746 := by exact prefixLift 803746
  have htrace : WordTrace (prefixWord ++ tailWord_803746) baseStart_803746 baseEnd_803746 := by
    simpa [prefixWord, tailWord_803746, baseEnd_803746] using wordTrace_append hprefix tailTrace_803746
  have hstable : (prefixWord ++ tailWord_803746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803746).length < 2 ^ (prefixWord ++ tailWord_803746).sum := by decide
  have hdescent : baseEnd_803746 < baseStart_803746 := by decide
  rcases family_descends (prefixWord ++ tailWord_803746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803822 : List Nat := [4, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_803822 : Nat := 118140960795 + 803822 * 2 ^ 59
def prefixEnd_803822 : Nat := 4983230072969 + 3 ^ 40 * 803822 * 2
def baseEnd_803822 : Nat := 366886263696408245714041

theorem tailTrace_803822 : CollatzResearch.WordTrace tailWord_803822 prefixEnd_803822 366886263696408245714041 := by
  unfold tailWord_803822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3664724611737206339142715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19545197929265100475427813 3664724611737206339142715)
  ·
    refine ⟨5497086917605809508714073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3664724611737206339142715 5497086917605809508714073)
    ·
      refine ⟨4122815188204357131535555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5497086917605809508714073 4122815188204357131535555)
      ·
        refine ⟨6184222782306535697303333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4122815188204357131535555 6184222782306535697303333)
        ·
          refine ⟨1159541771682475443244375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6184222782306535697303333 1159541771682475443244375)
          ·
            refine ⟨1739312657523713164866563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159541771682475443244375 1739312657523713164866563)
            ·
              refine ⟨2608968986285569747299845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739312657523713164866563 2608968986285569747299845)
              ·
                refine ⟨489181684928544327618721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2608968986285569747299845 489181684928544327618721)
                ·
                  refine ⟨366886263696408245714041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489181684928544327618721 366886263696408245714041)
                  ·
                    rfl

theorem cell20_803822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_803822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803822 prefixEnd_803822 := by exact prefixLift 803822
  have htrace : WordTrace (prefixWord ++ tailWord_803822) baseStart_803822 baseEnd_803822 := by
    simpa [prefixWord, tailWord_803822, baseEnd_803822] using wordTrace_append hprefix tailTrace_803822
  have hstable : (prefixWord ++ tailWord_803822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803822).length < 2 ^ (prefixWord ++ tailWord_803822).sum := by decide
  have hdescent : baseEnd_803822 < baseStart_803822 := by decide
  rcases family_descends (prefixWord ++ tailWord_803822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803850 : List Nat := [3, 1, 2, 2, 3, 2, 3, 4]
def baseStart_803850 : Nat := 118140960795 + 803850 * 2 ^ 59
def prefixEnd_803850 : Nat := 4983230072969 + 3 ^ 40 * 803850 * 2
def baseEnd_803850 : Nat := 122299681219788197593531

theorem tailTrace_803850 : CollatzResearch.WordTrace tailWord_803850 prefixEnd_803850 122299681219788197593531 := by
  unfold tailWord_803850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329704534449052873790251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19545878758530807663440669 7329704534449052873790251)
  ·
    refine ⟨10994556801673579310685377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7329704534449052873790251 10994556801673579310685377)
    ·
      refine ⟨8245917601255184483014033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10994556801673579310685377 8245917601255184483014033)
      ·
        refine ⟨6184438200941388362260525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8245917601255184483014033 6184438200941388362260525)
        ·
          refine ⟨2319164325353020635847697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6184438200941388362260525 2319164325353020635847697)
          ·
            refine ⟨1739373244014765476885773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319164325353020635847697 1739373244014765476885773)
            ·
              refine ⟨652264966505537053832165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1739373244014765476885773 652264966505537053832165)
              ·
                refine ⟨122299681219788197593531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652264966505537053832165 122299681219788197593531)
                ·
                  rfl

theorem cell20_803850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_803850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803850 prefixEnd_803850 := by exact prefixLift 803850
  have htrace : WordTrace (prefixWord ++ tailWord_803850) baseStart_803850 baseEnd_803850 := by
    simpa [prefixWord, tailWord_803850, baseEnd_803850] using wordTrace_append hprefix tailTrace_803850
  have hstable : (prefixWord ++ tailWord_803850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803850).length < 2 ^ (prefixWord ++ tailWord_803850).sum := by decide
  have hdescent : baseEnd_803850 < baseStart_803850 := by decide
  rcases family_descends (prefixWord ++ tailWord_803850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803874 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_803874 : Nat := 118140960795 + 803874 * 2 ^ 59
def prefixEnd_803874 : Nat := 4983230072969 + 3 ^ 40 * 803874 * 2
def baseEnd_803874 : Nat := 366909997913327175980495

theorem tailTrace_803874 : CollatzResearch.WordTrace tailWord_803874 prefixEnd_803874 366909997913327175980495 := by
  unfold tailWord_803874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329923372427315898508669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19546462326472842396023117 7329923372427315898508669)
  ·
    refine ⟨2748721264660243461940751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7329923372427315898508669 2748721264660243461940751)
    ·
      refine ⟨4123081896990365192911127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2748721264660243461940751 4123081896990365192911127)
      ·
        refine ⟨6184622845485547789366691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4123081896990365192911127 6184622845485547789366691)
        ·
          refine ⟨9276934268228321684050037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6184622845485547789366691 9276934268228321684050037)
          ·
            refine ⟨869712587646405157879691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9276934268228321684050037 869712587646405157879691)
            ·
              refine ⟨1304568881469607736819537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869712587646405157879691 1304568881469607736819537)
              ·
                refine ⟨978426661102205802614653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304568881469607736819537 978426661102205802614653)
                ·
                  refine ⟨366909997913327175980495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978426661102205802614653 366909997913327175980495)
                  ·
                    rfl

theorem cell20_803874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_803874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803874 prefixEnd_803874 := by exact prefixLift 803874
  have htrace : WordTrace (prefixWord ++ tailWord_803874) baseStart_803874 baseEnd_803874 := by
    simpa [prefixWord, tailWord_803874, baseEnd_803874] using wordTrace_append hprefix tailTrace_803874
  have hstable : (prefixWord ++ tailWord_803874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803874).length < 2 ^ (prefixWord ++ tailWord_803874).sum := by decide
  have hdescent : baseEnd_803874 < baseStart_803874 := by decide
  rcases family_descends (prefixWord ++ tailWord_803874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803899 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_803899 : Nat := 118140960795 + 803899 * 2 ^ 59
def prefixEnd_803899 : Nat := 4983230072969 + 3 ^ 40 * 803899 * 2
def baseEnd_803899 : Nat := 366921408594538200147059

theorem tailTrace_803899 : CollatzResearch.WordTrace tailWord_803899 prefixEnd_803899 366921408594538200147059 := by
  unfold tailWord_803899
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320605314618692863694751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19547070209745795242463167 29320605314618692863694751)
  ·
    refine ⟨43980907971928039295542127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29320605314618692863694751 43980907971928039295542127)
    ·
      refine ⟨65971361957892058943313191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43980907971928039295542127 65971361957892058943313191)
      ·
        refine ⟨98957042936838088414969787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65971361957892058943313191 98957042936838088414969787)
        ·
          refine ⟨148435564405257132622454681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98957042936838088414969787 148435564405257132622454681)
          ·
            refine ⟨111326673303942849466841011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148435564405257132622454681 111326673303942849466841011)
            ·
              refine ⟨166990009955914274200261517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111326673303942849466841011 166990009955914274200261517)
              ·
                refine ⟨62621253733467852825098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166990009955914274200261517 62621253733467852825098069)
                ·
                  refine ⟨366921408594538200147059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62621253733467852825098069 366921408594538200147059)
                  ·
                    rfl

theorem cell20_803899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_803899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803899 prefixEnd_803899 := by exact prefixLift 803899
  have htrace : WordTrace (prefixWord ++ tailWord_803899) baseStart_803899 baseEnd_803899 := by
    simpa [prefixWord, tailWord_803899, baseEnd_803899] using wordTrace_append hprefix tailTrace_803899
  have hstable : (prefixWord ++ tailWord_803899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803899).length < 2 ^ (prefixWord ++ tailWord_803899).sum := by decide
  have hdescent : baseEnd_803899 < baseStart_803899 := by decide
  rcases family_descends (prefixWord ++ tailWord_803899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803905 : List Nat := [1, 2, 5, 1, 3, 2, 2, 4]
def baseStart_803905 : Nat := 118140960795 + 803905 * 2 ^ 59
def prefixEnd_803905 : Nat := 4983230072969 + 3 ^ 40 * 803905 * 2
def baseEnd_803905 : Nat := 122308049052676281982345

theorem tailTrace_803905 : CollatzResearch.WordTrace tailWord_803905 prefixEnd_803905 122308049052676281982345 := by
  unfold tailWord_803905
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320824152596955888413169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19547216101731303925608779 29320824152596955888413169)
  ·
    refine ⟨21990618114447716916309877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29320824152596955888413169 21990618114447716916309877)
    ·
      refine ⟨2061620448229473460904051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21990618114447716916309877 2061620448229473460904051)
      ·
        refine ⟨3092430672344210191356077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061620448229473460904051 3092430672344210191356077)
        ·
          refine ⟨1159661502129078821758529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3092430672344210191356077 1159661502129078821758529)
          ·
            refine ⟨869746126596809116318897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1159661502129078821758529 869746126596809116318897)
            ·
              refine ⟨652309594947606837239173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869746126596809116318897 652309594947606837239173)
              ·
                refine ⟨122308049052676281982345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652309594947606837239173 122308049052676281982345)
                ·
                  rfl

theorem cell20_803905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_803905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803905 prefixEnd_803905 := by exact prefixLift 803905
  have htrace : WordTrace (prefixWord ++ tailWord_803905) baseStart_803905 baseEnd_803905 := by
    simpa [prefixWord, tailWord_803905, baseEnd_803905] using wordTrace_append hprefix tailTrace_803905
  have hstable : (prefixWord ++ tailWord_803905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803905).length < 2 ^ (prefixWord ++ tailWord_803905).sum := by decide
  have hdescent : baseEnd_803905 < baseStart_803905 := by decide
  rcases family_descends (prefixWord ++ tailWord_803905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803909 : List Nat := [1, 3, 1, 1, 1, 3, 6, 4]
def baseStart_803909 : Nat := 118140960795 + 803909 * 2 ^ 59
def prefixEnd_803909 : Nat := 4983230072969 + 3 ^ 40 * 803909 * 2
def baseEnd_803909 : Nat := 122308657622340869937895

theorem tailTrace_803909 : CollatzResearch.WordTrace tailWord_803909 prefixEnd_803909 122308657622340869937895 := by
  unfold tailWord_803909
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320970044582464571558781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19547313363054976381039187 29320970044582464571558781)
  ·
    refine ⟨10995363766718424214334543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29320970044582464571558781 10995363766718424214334543)
    ·
      refine ⟨16493045650077636321501815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10995363766718424214334543 16493045650077636321501815)
      ·
        refine ⟨24739568475116454482252723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16493045650077636321501815 24739568475116454482252723)
        ·
          refine ⟨37109352712674681723379085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24739568475116454482252723 37109352712674681723379085)
          ·
            refine ⟨13916007267253005646267157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37109352712674681723379085 13916007267253005646267157)
            ·
              refine ⟨652312840652484639668773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13916007267253005646267157 652312840652484639668773)
              ·
                refine ⟨122308657622340869937895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652312840652484639668773 122308657622340869937895)
                ·
                  rfl

theorem cell20_803909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_803909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803909 prefixEnd_803909 := by exact prefixLift 803909
  have htrace : WordTrace (prefixWord ++ tailWord_803909) baseStart_803909 baseEnd_803909 := by
    simpa [prefixWord, tailWord_803909, baseEnd_803909] using wordTrace_append hprefix tailTrace_803909
  have hstable : (prefixWord ++ tailWord_803909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803909).length < 2 ^ (prefixWord ++ tailWord_803909).sum := by decide
  have hdescent : baseEnd_803909 < baseStart_803909 := by decide
  rcases family_descends (prefixWord ++ tailWord_803909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803950 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_803950 : Nat := 118140960795 + 803950 * 2 ^ 59
def prefixEnd_803950 : Nat := 4983230072969 + 3 ^ 40 * 803950 * 2
def baseEnd_803950 : Nat := 366944686384208689446851

theorem tailTrace_803950 : CollatzResearch.WordTrace tailWord_803950 prefixEnd_803950 366944686384208689446851 := by
  unfold tailWord_803950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665308179679241071725163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19548310291622619049200869 3665308179679241071725163)
  ·
    refine ⟨5497962269518861607587745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3665308179679241071725163 5497962269518861607587745)
    ·
      refine ⟨4123471702139146205690809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5497962269518861607587745 4123471702139146205690809)
      ·
        refine ⟨3092603776604359654268107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4123471702139146205690809 3092603776604359654268107)
        ·
          refine ⟨4638905664906539481402161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092603776604359654268107 4638905664906539481402161)
          ·
            refine ⟨3479179248679904611051621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4638905664906539481402161 3479179248679904611051621)
            ·
              refine ⟨652346109127482114572179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3479179248679904611051621 652346109127482114572179)
              ·
                refine ⟨978519163691223171858269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652346109127482114572179 978519163691223171858269)
                ·
                  refine ⟨366944686384208689446851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978519163691223171858269 366944686384208689446851)
                  ·
                    rfl

theorem cell20_803950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_803950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803950 prefixEnd_803950 := by exact prefixLift 803950
  have htrace : WordTrace (prefixWord ++ tailWord_803950) baseStart_803950 baseEnd_803950 := by
    simpa [prefixWord, tailWord_803950, baseEnd_803950] using wordTrace_append hprefix tailTrace_803950
  have hstable : (prefixWord ++ tailWord_803950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803950).length < 2 ^ (prefixWord ++ tailWord_803950).sum := by decide
  have hdescent : baseEnd_803950 < baseStart_803950 := by decide
  rcases family_descends (prefixWord ++ tailWord_803950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803968 : List Nat := [2, 1, 1, 2, 1, 3, 4, 6]
def baseStart_803968 : Nat := 118140960795 + 803968 * 2 ^ 59
def prefixEnd_803968 : Nat := 4983230072969 + 3 ^ 40 * 803968 * 2
def baseEnd_803968 : Nat := 122317634024893542282259

theorem tailTrace_803968 : CollatzResearch.WordTrace tailWord_803968 prefixEnd_803968 122317634024893542282259 := by
  unfold tailWord_803968
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661560975684358823978279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19548747967579145098637705 14661560975684358823978279)
  ·
    refine ⟨21992341463526538235967419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14661560975684358823978279 21992341463526538235967419)
    ·
      refine ⟨32988512195289807353951129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21992341463526538235967419 32988512195289807353951129)
      ·
        refine ⟨24741384146467355515463347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32988512195289807353951129 24741384146467355515463347)
        ·
          refine ⟨37112076219701033273195021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24741384146467355515463347 37112076219701033273195021)
          ·
            refine ⟨13917028582387887477448133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37112076219701033273195021 13917028582387887477448133)
            ·
              refine ⟨2609442859197728902021525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13917028582387887477448133 2609442859197728902021525)
              ·
                refine ⟨122317634024893542282259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2609442859197728902021525 122317634024893542282259)
                ·
                  rfl

theorem cell20_803968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_803968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_803968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_803968 prefixEnd_803968 := by exact prefixLift 803968
  have htrace : WordTrace (prefixWord ++ tailWord_803968) baseStart_803968 baseEnd_803968 := by
    simpa [prefixWord, tailWord_803968, baseEnd_803968] using wordTrace_append hprefix tailTrace_803968
  have hstable : (prefixWord ++ tailWord_803968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803968).length < 2 ^ (prefixWord ++ tailWord_803968).sum := by decide
  have hdescent : baseEnd_803968 < baseStart_803968 := by decide
  rcases family_descends (prefixWord ++ tailWord_803968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804023 : List Nat := [1, 1, 3, 1, 4, 1, 5, 4]
def baseStart_804023 : Nat := 118140960795 + 804023 * 2 ^ 59
def prefixEnd_804023 : Nat := 4983230072969 + 3 ^ 40 * 804023 * 2
def baseEnd_804023 : Nat := 122326001857781626671073

theorem tailTrace_804023 : CollatzResearch.WordTrace tailWord_804023 prefixEnd_804023 122326001857781626671073 := by
  unfold tailWord_804023
  simp only [CollatzResearch.WordTrace]
  refine ⟨29325127966169462041208723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19550085310779641360805815 29325127966169462041208723)
  ·
    refine ⟨43987691949254193061813085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29325127966169462041208723 43987691949254193061813085)
    ·
      refine ⟨16495384480970322398179907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43987691949254193061813085 16495384480970322398179907)
      ·
        refine ⟨24743076721455483597269861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16495384480970322398179907 24743076721455483597269861)
        ·
          refine ⟨4639326885272903174488099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24743076721455483597269861 4639326885272903174488099)
          ·
            refine ⟨6958990327909354761732149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639326885272903174488099 6958990327909354761732149)
            ·
              refine ⟨652405343241502008912389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6958990327909354761732149 652405343241502008912389)
              ·
                refine ⟨122326001857781626671073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652405343241502008912389 122326001857781626671073)
                ·
                  rfl

theorem cell20_804023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_804023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804023 prefixEnd_804023 := by exact prefixLift 804023
  have htrace : WordTrace (prefixWord ++ tailWord_804023) baseStart_804023 baseEnd_804023 := by
    simpa [prefixWord, tailWord_804023, baseEnd_804023] using wordTrace_append hprefix tailTrace_804023
  have hstable : (prefixWord ++ tailWord_804023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804023).length < 2 ^ (prefixWord ++ tailWord_804023).sum := by decide
  have hdescent : baseEnd_804023 < baseStart_804023 := by decide
  rcases family_descends (prefixWord ++ tailWord_804023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804051 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_804051 : Nat := 118140960795 + 804051 * 2 ^ 59
def prefixEnd_804051 : Nat := 4983230072969 + 3 ^ 40 * 804051 * 2
def baseEnd_804051 : Nat := 366990785536301227079771

theorem tailTrace_804051 : CollatzResearch.WordTrace tailWord_804051 prefixEnd_804051 366990785536301227079771 := by
  unfold tailWord_804051
  simp only [CollatzResearch.WordTrace]
  refine ⟨29326149210068022823228007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19550766140045348548818671 29326149210068022823228007)
  ·
    refine ⟨43989223815102034234842011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29326149210068022823228007 43989223815102034234842011)
    ·
      refine ⟨65983835722653051352263017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43989223815102034234842011 65983835722653051352263017)
      ·
        refine ⟨49487876791989788514197263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65983835722653051352263017 49487876791989788514197263)
        ·
          refine ⟨74231815187984682771295895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49487876791989788514197263 74231815187984682771295895)
          ·
            refine ⟨111347722781977024156943843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74231815187984682771295895 111347722781977024156943843)
            ·
              refine ⟨167021584172965536235415765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111347722781977024156943843 167021584172965536235415765)
              ·
                refine ⟨3914568379053879755517557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167021584172965536235415765 3914568379053879755517557)
                ·
                  refine ⟨366990785536301227079771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3914568379053879755517557 366990785536301227079771)
                  ·
                    rfl

theorem cell20_804051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_804051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804051 prefixEnd_804051 := by exact prefixLift 804051
  have htrace : WordTrace (prefixWord ++ tailWord_804051) baseStart_804051 baseEnd_804051 := by
    simpa [prefixWord, tailWord_804051, baseEnd_804051] using wordTrace_append hprefix tailTrace_804051
  have hstable : (prefixWord ++ tailWord_804051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804051).length < 2 ^ (prefixWord ++ tailWord_804051).sum := by decide
  have hdescent : baseEnd_804051 < baseStart_804051 := by decide
  rcases family_descends (prefixWord ++ tailWord_804051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804068 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_804068 : Nat := 118140960795 + 804068 * 2 ^ 59
def prefixEnd_804068 : Nat := 4983230072969 + 3 ^ 40 * 804068 * 2
def baseEnd_804068 : Nat := 366998544799524723513035

theorem tailTrace_804068 : CollatzResearch.WordTrace tailWord_804068 prefixEnd_804068 366998544799524723513035 := by
  unfold tailWord_804068
  simp only [CollatzResearch.WordTrace]
  refine ⟨14663384625503217363298429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19551179500670956484397905 14663384625503217363298429)
  ·
    refine ⟨5498769234563706511236911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14663384625503217363298429 5498769234563706511236911)
    ·
      refine ⟨8248153851845559766855367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5498769234563706511236911 8248153851845559766855367)
      ·
        refine ⟨12372230777768339650283051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248153851845559766855367 12372230777768339650283051)
        ·
          refine ⟨18558346166652509475424577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12372230777768339650283051 18558346166652509475424577)
          ·
            refine ⟨13918759624989382106568433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18558346166652509475424577 13918759624989382106568433)
            ·
              refine ⟨10439069718742036579926325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13918759624989382106568433 10439069718742036579926325)
              ·
                refine ⟨978662786132065929368093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10439069718742036579926325 978662786132065929368093)
                ·
                  refine ⟨366998544799524723513035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978662786132065929368093 366998544799524723513035)
                  ·
                    rfl

theorem cell20_804068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_804068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804068 prefixEnd_804068 := by exact prefixLift 804068
  have htrace : WordTrace (prefixWord ++ tailWord_804068) baseStart_804068 baseEnd_804068 := by
    simpa [prefixWord, tailWord_804068, baseEnd_804068] using wordTrace_append hprefix tailTrace_804068
  have hstable : (prefixWord ++ tailWord_804068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804068).length < 2 ^ (prefixWord ++ tailWord_804068).sum := by decide
  have hdescent : baseEnd_804068 < baseStart_804068 := by decide
  rcases family_descends (prefixWord ++ tailWord_804068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804075 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_804075 : Nat := 118140960795 + 804075 * 2 ^ 59
def prefixEnd_804075 : Nat := 4983230072969 + 3 ^ 40 * 804075 * 2
def baseEnd_804075 : Nat := 367001739790263810279673

theorem tailTrace_804075 : CollatzResearch.WordTrace tailWord_804075 prefixEnd_804075 367001739790263810279673 := by
  unfold tailWord_804075
  simp only [CollatzResearch.WordTrace]
  refine ⟨29327024561981074922101679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19551349707987383281401119 29327024561981074922101679)
  ·
    refine ⟨43990536842971612383152519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29327024561981074922101679 43990536842971612383152519)
    ·
      refine ⟨65985805264457418574728779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43990536842971612383152519 65985805264457418574728779)
      ·
        refine ⟨98978707896686127862093169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65985805264457418574728779 98978707896686127862093169)
        ·
          refine ⟨74234030922514595896569877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98978707896686127862093169 74234030922514595896569877)
          ·
            refine ⟨3479720199492871682651713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74234030922514595896569877 3479720199492871682651713)
            ·
              refine ⟨2609790149619653761988785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479720199492871682651713 2609790149619653761988785)
              ·
                refine ⟨1957342612214740321491589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609790149619653761988785 1957342612214740321491589)
                ·
                  refine ⟨367001739790263810279673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957342612214740321491589 367001739790263810279673)
                  ·
                    rfl

theorem cell20_804075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_804075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804075 prefixEnd_804075 := by exact prefixLift 804075
  have htrace : WordTrace (prefixWord ++ tailWord_804075) baseStart_804075 baseEnd_804075 := by
    simpa [prefixWord, tailWord_804075, baseEnd_804075] using wordTrace_append hprefix tailTrace_804075
  have hstable : (prefixWord ++ tailWord_804075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804075).length < 2 ^ (prefixWord ++ tailWord_804075).sum := by decide
  have hdescent : baseEnd_804075 < baseStart_804075 := by decide
  rcases family_descends (prefixWord ++ tailWord_804075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804089 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_804089 : Nat := 118140960795 + 804089 * 2 ^ 59
def prefixEnd_804089 : Nat := 4983230072969 + 3 ^ 40 * 804089 * 2
def baseEnd_804089 : Nat := 367008129771741983812949

theorem tailTrace_804089 : CollatzResearch.WordTrace tailWord_804089 prefixEnd_804089 367008129771741983812949 := by
  unfold tailWord_804089
  simp only [CollatzResearch.WordTrace]
  refine ⟨29327535183930355313111321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19551690122620236875407547 29327535183930355313111321)
  ·
    refine ⟨21995651387947766484833491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29327535183930355313111321 21995651387947766484833491)
    ·
      refine ⟨32993477081921649727250237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21995651387947766484833491 32993477081921649727250237)
      ·
        refine ⟨12372553905720618647718839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32993477081921649727250237 12372553905720618647718839)
        ·
          refine ⟨18558830858580927971578259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12372553905720618647718839 18558830858580927971578259)
          ·
            refine ⟨27838246287871391957367389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18558830858580927971578259 27838246287871391957367389)
            ·
              refine ⟨10439342357951771984012771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27838246287871391957367389 10439342357951771984012771)
              ·
                refine ⟨15659013536927657976019157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439342357951771984012771 15659013536927657976019157)
                ·
                  refine ⟨367008129771741983812949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15659013536927657976019157 367008129771741983812949)
                  ·
                    rfl

theorem cell20_804089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_804089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804089 prefixEnd_804089 := by exact prefixLift 804089
  have htrace : WordTrace (prefixWord ++ tailWord_804089) baseStart_804089 baseEnd_804089 := by
    simpa [prefixWord, tailWord_804089, baseEnd_804089] using wordTrace_append hprefix tailTrace_804089
  have hstable : (prefixWord ++ tailWord_804089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804089).length < 2 ^ (prefixWord ++ tailWord_804089).sum := by decide
  have hdescent : baseEnd_804089 < baseStart_804089 := by decide
  rcases family_descends (prefixWord ++ tailWord_804089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804106 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_804106 : Nat := 118140960795 + 804106 * 2 ^ 59
def prefixEnd_804106 : Nat := 4983230072969 + 3 ^ 40 * 804106 * 2
def baseEnd_804106 : Nat := 367015889034965480246213

theorem tailTrace_804106 : CollatzResearch.WordTrace tailWord_804106 prefixEnd_804106 367015889034965480246213 := by
  unfold tailWord_804106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332038806217191804120043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19552103483245844810986781 7332038806217191804120043)
  ·
    refine ⟨10998058209325787706180065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7332038806217191804120043 10998058209325787706180065)
    ·
      refine ⟨8248543656994340779635049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10998058209325787706180065 8248543656994340779635049)
      ·
        refine ⟨6186407742745755584726287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8248543656994340779635049 6186407742745755584726287)
        ·
          refine ⟨9279611614118633377089431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186407742745755584726287 9279611614118633377089431)
          ·
            refine ⟨13919417421177950065634147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279611614118633377089431 13919417421177950065634147)
            ·
              refine ⟨20879126131766925098451221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919417421177950065634147 20879126131766925098451221)
              ·
                refine ⟨978709037426574613989901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20879126131766925098451221 978709037426574613989901)
                ·
                  refine ⟨367015889034965480246213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978709037426574613989901 367015889034965480246213)
                  ·
                    rfl

theorem cell20_804106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_804106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804106 prefixEnd_804106 := by exact prefixLift 804106
  have htrace : WordTrace (prefixWord ++ tailWord_804106) baseStart_804106 baseEnd_804106 := by
    simpa [prefixWord, tailWord_804106, baseEnd_804106] using wordTrace_append hprefix tailTrace_804106
  have hstable : (prefixWord ++ tailWord_804106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804106).length < 2 ^ (prefixWord ++ tailWord_804106).sum := by decide
  have hdescent : baseEnd_804106 < baseStart_804106 := by decide
  rcases family_descends (prefixWord ++ tailWord_804106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804120 : List Nat := [2, 1, 2, 3, 1, 3, 1, 7]
def baseStart_804120 : Nat := 118140960795 + 804120 * 2 ^ 59
def prefixEnd_804120 : Nat := 4983230072969 + 3 ^ 40 * 804120 * 2
def baseEnd_804120 : Nat := 122340759672147884593163

theorem tailTrace_804120 : CollatzResearch.WordTrace tailWord_804120 prefixEnd_804120 122340759672147884593163 := by
  unfold tailWord_804120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14664332923409023803744907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19552443897878698404993209 14664332923409023803744907)
  ·
    refine ⟨21996499385113535705617361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14664332923409023803744907 21996499385113535705617361)
    ·
      refine ⟨16497374538835151779213021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21996499385113535705617361 16497374538835151779213021)
      ·
        refine ⟨6186515452063181917204883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16497374538835151779213021 6186515452063181917204883)
        ·
          refine ⟨9279773178094772875807325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186515452063181917204883 9279773178094772875807325)
          ·
            refine ⟨3479914941785539828427747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9279773178094772875807325 3479914941785539828427747)
            ·
              refine ⟨5219872412678309742641621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479914941785539828427747 5219872412678309742641621)
              ·
                refine ⟨122340759672147884593163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5219872412678309742641621 122340759672147884593163)
                ·
                  rfl

theorem cell20_804120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_804120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804120 prefixEnd_804120 := by exact prefixLift 804120
  have htrace : WordTrace (prefixWord ++ tailWord_804120) baseStart_804120 baseEnd_804120 := by
    simpa [prefixWord, tailWord_804120, baseEnd_804120] using wordTrace_append hprefix tailTrace_804120
  have hstable : (prefixWord ++ tailWord_804120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804120).length < 2 ^ (prefixWord ++ tailWord_804120).sum := by decide
  have hdescent : baseEnd_804120 < baseStart_804120 := by decide
  rcases family_descends (prefixWord ++ tailWord_804120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804161 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 3]
def baseStart_804161 : Nat := 118140960795 + 804161 * 2 ^ 59
def prefixEnd_804161 : Nat := 4983230072969 + 3 ^ 40 * 804161 * 2
def baseEnd_804161 : Nat := 367040992533629733412655

theorem tailTrace_804161 : CollatzResearch.WordTrace tailWord_804161 prefixEnd_804161 367040992533629733412655 := by
  unfold tailWord_804161
  simp only [CollatzResearch.WordTrace]
  refine ⟨29330161239669511609732337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19553440826446341073154891 29330161239669511609732337)
  ·
    refine ⟨21997620929752133707299253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29330161239669511609732337 21997620929752133707299253)
    ·
      refine ⟨2062276962164262535059305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21997620929752133707299253 2062276962164262535059305)
      ·
        refine ⟨1546707721623196901294479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2062276962164262535059305 1546707721623196901294479)
        ·
          refine ⟨2320061582434795351941719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546707721623196901294479 2320061582434795351941719)
          ·
            refine ⟨3480092373652193027912579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320061582434795351941719 3480092373652193027912579)
            ·
              refine ⟨5220138560478289541868869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480092373652193027912579 5220138560478289541868869)
              ·
                refine ⟨978775980089679289100413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5220138560478289541868869 978775980089679289100413)
                ·
                  refine ⟨367040992533629733412655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978775980089679289100413 367040992533629733412655)
                  ·
                    rfl

theorem cell20_804161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_804161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804161 prefixEnd_804161 := by exact prefixLift 804161
  have htrace : WordTrace (prefixWord ++ tailWord_804161) baseStart_804161 baseEnd_804161 := by
    simpa [prefixWord, tailWord_804161, baseEnd_804161] using wordTrace_append hprefix tailTrace_804161
  have hstable : (prefixWord ++ tailWord_804161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804161).length < 2 ^ (prefixWord ++ tailWord_804161).sum := by decide
  have hdescent : baseEnd_804161 < baseStart_804161 := by decide
  rcases family_descends (prefixWord ++ tailWord_804161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804164 : List Nat := [2, 3, 4, 1, 1, 2, 1, 4, 2]
def baseStart_804164 : Nat := 118140960795 + 804164 * 2 ^ 59
def prefixEnd_804164 : Nat := 4983230072969 + 3 ^ 40 * 804164 * 2
def baseEnd_804164 : Nat := 367042361815375056312643

theorem tailTrace_804164 : CollatzResearch.WordTrace tailWord_804164 prefixEnd_804164 367042361815375056312643 := by
  unfold tailWord_804164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14665135329329321561045773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19553513772439095414727697 14665135329329321561045773)
  ·
    refine ⟨5499425748498495585392165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14665135329329321561045773 5499425748498495585392165)
    ·
      refine ⟨1031142327843467922261031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5499425748498495585392165 1031142327843467922261031)
      ·
        refine ⟨1546713491765201883391547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031142327843467922261031 1546713491765201883391547)
        ·
          refine ⟨2320070237647802825087321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546713491765201883391547 2320070237647802825087321)
          ·
            refine ⟨1740052678235852118815491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2320070237647802825087321 1740052678235852118815491)
            ·
              refine ⟨2610079017353778178223237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740052678235852118815491 2610079017353778178223237)
              ·
                refine ⟨489389815753833408416857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2610079017353778178223237 489389815753833408416857)
                ·
                  refine ⟨367042361815375056312643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489389815753833408416857 367042361815375056312643)
                  ·
                    rfl

theorem cell20_804164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_804164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804164 prefixEnd_804164 := by exact prefixLift 804164
  have htrace : WordTrace (prefixWord ++ tailWord_804164) baseStart_804164 baseEnd_804164 := by
    simpa [prefixWord, tailWord_804164, baseEnd_804164] using wordTrace_append hprefix tailTrace_804164
  have hstable : (prefixWord ++ tailWord_804164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804164).length < 2 ^ (prefixWord ++ tailWord_804164).sum := by decide
  have hdescent : baseEnd_804164 < baseStart_804164 := by decide
  rcases family_descends (prefixWord ++ tailWord_804164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804165 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_804165 : Nat := 118140960795 + 804165 * 2 ^ 59
def prefixEnd_804165 : Nat := 4983230072969 + 3 ^ 40 * 804165 * 2
def baseEnd_804165 : Nat := 367042818242623497279305

theorem tailTrace_804165 : CollatzResearch.WordTrace tailWord_804165 prefixEnd_804165 367042818242623497279305 := by
  unfold tailWord_804165
  simp only [CollatzResearch.WordTrace]
  refine ⟨29330307131655020292877949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19553538087770013528585299 29330307131655020292877949)
  ·
    refine ⟨10998865174370632609829231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29330307131655020292877949 10998865174370632609829231)
    ·
      refine ⟨16498297761555948914743847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10998865174370632609829231 16498297761555948914743847)
      ·
        refine ⟨24747446642333923372115771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16498297761555948914743847 24747446642333923372115771)
        ·
          refine ⟨37121169963500885058173657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24747446642333923372115771 37121169963500885058173657)
          ·
            refine ⟨27840877472625663793630243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37121169963500885058173657 27840877472625663793630243)
            ·
              refine ⟨41761316208938495690445365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27840877472625663793630243 41761316208938495690445365)
              ·
                refine ⟨3915123394587983970979253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41761316208938495690445365 3915123394587983970979253)
                ·
                  refine ⟨367042818242623497279305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915123394587983970979253 367042818242623497279305)
                  ·
                    rfl

theorem cell20_804165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_804165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804165 prefixEnd_804165 := by exact prefixLift 804165
  have htrace : WordTrace (prefixWord ++ tailWord_804165) baseStart_804165 baseEnd_804165 := by
    simpa [prefixWord, tailWord_804165, baseEnd_804165] using wordTrace_append hprefix tailTrace_804165
  have hstable : (prefixWord ++ tailWord_804165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804165).length < 2 ^ (prefixWord ++ tailWord_804165).sum := by decide
  have hdescent : baseEnd_804165 < baseStart_804165 := by decide
  rcases family_descends (prefixWord ++ tailWord_804165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804202 : List Nat := [3, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_804202 : Nat := 118140960795 + 804202 * 2 ^ 59
def prefixEnd_804202 : Nat := 4983230072969 + 3 ^ 40 * 804202 * 2
def baseEnd_804202 : Nat := 367059706050815813045821

theorem tailTrace_804202 : CollatzResearch.WordTrace tailWord_804202 prefixEnd_804202 367059706050815813045821 := by
  unfold tailWord_804202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332914158130243902993715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19554437755013983741316573 7332914158130243902993715)
  ·
    refine ⟨10999371237195365854490573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7332914158130243902993715 10999371237195365854490573)
    ·
      refine ⟨4124764213948262195433965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10999371237195365854490573 4124764213948262195433965)
      ·
        refine ⟨1546786580230598323287737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4124764213948262195433965 1546786580230598323287737)
        ·
          refine ⟨1160089935172948742465803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1546786580230598323287737 1160089935172948742465803)
          ·
            refine ⟨1740134902759423113698705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160089935172948742465803 1740134902759423113698705)
            ·
              refine ⟨1305101177069567335274029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740134902759423113698705 1305101177069567335274029)
              ·
                refine ⟨489412941401087750727761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1305101177069567335274029 489412941401087750727761)
                ·
                  refine ⟨367059706050815813045821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489412941401087750727761 367059706050815813045821)
                  ·
                    rfl

theorem cell20_804202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_804202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804202 prefixEnd_804202 := by exact prefixLift 804202
  have htrace : WordTrace (prefixWord ++ tailWord_804202) baseStart_804202 baseEnd_804202 := by
    simpa [prefixWord, tailWord_804202, baseEnd_804202] using wordTrace_append hprefix tailTrace_804202
  have hstable : (prefixWord ++ tailWord_804202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804202).length < 2 ^ (prefixWord ++ tailWord_804202).sum := by decide
  have hdescent : baseEnd_804202 < baseStart_804202 := by decide
  rcases family_descends (prefixWord ++ tailWord_804202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804213 : List Nat := [1, 3, 4, 1, 3, 1, 7]
def baseStart_804213 : Nat := 118140960795 + 804213 * 2 ^ 59
def prefixEnd_804213 : Nat := 4983230072969 + 3 ^ 40 * 804213 * 2
def baseEnd_804213 : Nat := 40784969638949851519901

theorem tailTrace_804213 : CollatzResearch.WordTrace tailWord_804213 prefixEnd_804213 40784969638949851519901 := by
  unfold tailWord_804213
  simp only [CollatzResearch.WordTrace]
  refine ⟨29332057835481124490625293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19554705223654082993750195 29332057835481124490625293)
  ·
    refine ⟨10999521688305421683984485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29332057835481124490625293 10999521688305421683984485)
    ·
      refine ⟨2062410316557266565747091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10999521688305421683984485 2062410316557266565747091)
      ·
        refine ⟨3093615474835899848620637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062410316557266565747091 3093615474835899848620637)
        ·
          refine ⟨1160105803063462443232739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3093615474835899848620637 1160105803063462443232739)
          ·
            refine ⟨1740158704595193664849109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160105803063462443232739 1740158704595193664849109)
            ·
              refine ⟨40784969638949851519901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1740158704595193664849109 40784969638949851519901)
              ·
                rfl

theorem cell20_804213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 7].length) (baseStart_804213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804213 prefixEnd_804213 := by exact prefixLift 804213
  have htrace : WordTrace (prefixWord ++ tailWord_804213) baseStart_804213 baseEnd_804213 := by
    simpa [prefixWord, tailWord_804213, baseEnd_804213] using wordTrace_append hprefix tailTrace_804213
  have hstable : (prefixWord ++ tailWord_804213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804213).length < 2 ^ (prefixWord ++ tailWord_804213).sum := by decide
  have hdescent : baseEnd_804213 < baseStart_804213 := by decide
  rcases family_descends (prefixWord ++ tailWord_804213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804227 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_804227 : Nat := 118140960795 + 804227 * 2 ^ 59
def prefixEnd_804227 : Nat := 4983230072969 + 3 ^ 40 * 804227 * 2
def baseEnd_804227 : Nat := 367071116732026837212385

theorem tailTrace_804227 : CollatzResearch.WordTrace tailWord_804227 prefixEnd_804227 367071116732026837212385 := by
  unfold tailWord_804227
  simp only [CollatzResearch.WordTrace]
  refine ⟨29332568457430404881634935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19555045638286936587756623 29332568457430404881634935)
  ·
    refine ⟨43998852686145607322452403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29332568457430404881634935 43998852686145607322452403)
    ·
      refine ⟨65998279029218410983678605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43998852686145607322452403 65998279029218410983678605)
      ·
        refine ⟨24749354635956904118879477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65998279029218410983678605 24749354635956904118879477)
        ·
          refine ⟨2320251997120959761144951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24749354635956904118879477 2320251997120959761144951)
          ·
            refine ⟨3480377995681439641717427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320251997120959761144951 3480377995681439641717427)
            ·
              refine ⟨5220566993522159462576141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480377995681439641717427 5220566993522159462576141)
              ·
                refine ⟨1957712622570809798466053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5220566993522159462576141 1957712622570809798466053)
                ·
                  refine ⟨367071116732026837212385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957712622570809798466053 367071116732026837212385)
                  ·
                    rfl

theorem cell20_804227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_804227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804227 prefixEnd_804227 := by exact prefixLift 804227
  have htrace : WordTrace (prefixWord ++ tailWord_804227) baseStart_804227 baseEnd_804227 := by
    simpa [prefixWord, tailWord_804227, baseEnd_804227] using wordTrace_append hprefix tailTrace_804227
  have hstable : (prefixWord ++ tailWord_804227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804227).length < 2 ^ (prefixWord ++ tailWord_804227).sum := by decide
  have hdescent : baseEnd_804227 < baseStart_804227 := by decide
  rcases family_descends (prefixWord ++ tailWord_804227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804244 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_804244 : Nat := 118140960795 + 804244 * 2 ^ 59
def prefixEnd_804244 : Nat := 4983230072969 + 3 ^ 40 * 804244 * 2
def baseEnd_804244 : Nat := 367078875995250333645649

theorem tailTrace_804244 : CollatzResearch.WordTrace tailWord_804244 prefixEnd_804244 367078875995250333645649 := by
  unfold tailWord_804244
  simp only [CollatzResearch.WordTrace]
  refine ⟨14666594249184408392501893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19555458998912544523335857 14666594249184408392501893)
  ·
    refine ⟨2749986421722076573594105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14666594249184408392501893 2749986421722076573594105)
    ·
      refine ⟨2062489816291557430195579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2749986421722076573594105 2062489816291557430195579)
      ·
        refine ⟨3093734724437336145293369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062489816291557430195579 3093734724437336145293369)
        ·
          refine ⟨2320301043328002108970027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3093734724437336145293369 2320301043328002108970027)
          ·
            refine ⟨3480451564992003163455041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320301043328002108970027 3480451564992003163455041)
            ·
              refine ⟨2610338673744002372591281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480451564992003163455041 2610338673744002372591281)
              ·
                refine ⟨1957754005308001779443461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610338673744002372591281 1957754005308001779443461)
                ·
                  refine ⟨367078875995250333645649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957754005308001779443461 367078875995250333645649)
                  ·
                    rfl

theorem cell20_804244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_804244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804244 prefixEnd_804244 := by exact prefixLift 804244
  have htrace : WordTrace (prefixWord ++ tailWord_804244) baseStart_804244 baseEnd_804244 := by
    simpa [prefixWord, tailWord_804244, baseEnd_804244] using wordTrace_append hprefix tailTrace_804244
  have hstable : (prefixWord ++ tailWord_804244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804244).length < 2 ^ (prefixWord ++ tailWord_804244).sum := by decide
  have hdescent : baseEnd_804244 < baseStart_804244 := by decide
  rcases family_descends (prefixWord ++ tailWord_804244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804258 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_804258 : Nat := 118140960795 + 804258 * 2 ^ 59
def prefixEnd_804258 : Nat := 4983230072969 + 3 ^ 40 * 804258 * 2
def baseEnd_804258 : Nat := 367085265976728507178925

theorem tailTrace_804258 : CollatzResearch.WordTrace tailWord_804258 prefixEnd_804258 367085265976728507178925 := by
  unfold tailWord_804258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333424780079524294003357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19555799413545398117342285 7333424780079524294003357)
  ·
    refine ⟨2750034292529821610251259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7333424780079524294003357 2750034292529821610251259)
    ·
      refine ⟨4125051438794732415376889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750034292529821610251259 4125051438794732415376889)
      ·
        refine ⟨3093788579096049311532667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4125051438794732415376889 3093788579096049311532667)
        ·
          refine ⟨4640682868644073967299001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3093788579096049311532667 4640682868644073967299001)
          ·
            refine ⟨3480512151483055475474251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4640682868644073967299001 3480512151483055475474251)
            ·
              refine ⟨5220768227224583213211377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480512151483055475474251 5220768227224583213211377)
              ·
                refine ⟨3915576170418437409908533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5220768227224583213211377 3915576170418437409908533)
                ·
                  refine ⟨367085265976728507178925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915576170418437409908533 367085265976728507178925)
                  ·
                    rfl

theorem cell20_804258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_804258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804258 prefixEnd_804258 := by exact prefixLift 804258
  have htrace : WordTrace (prefixWord ++ tailWord_804258) baseStart_804258 baseEnd_804258 := by
    simpa [prefixWord, tailWord_804258, baseEnd_804258] using wordTrace_append hprefix tailTrace_804258
  have hstable : (prefixWord ++ tailWord_804258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804258).length < 2 ^ (prefixWord ++ tailWord_804258).sum := by decide
  have hdescent : baseEnd_804258 < baseStart_804258 := by decide
  rcases family_descends (prefixWord ++ tailWord_804258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804279 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_804279 : Nat := 118140960795 + 804279 * 2 ^ 59
def prefixEnd_804279 : Nat := 4983230072969 + 3 ^ 40 * 804279 * 2
def baseEnd_804279 : Nat := 367094850948945767478839

theorem tailTrace_804279 : CollatzResearch.WordTrace tailWord_804279 prefixEnd_804279 367094850948945767478839 := by
  unfold tailWord_804279
  simp only [CollatzResearch.WordTrace]
  refine ⟨29334465053242017762527891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19556310035494678508351927 29334465053242017762527891)
  ·
    refine ⟨44001697579863026643791837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29334465053242017762527891 44001697579863026643791837)
    ·
      refine ⟨16500636592448634991421939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44001697579863026643791837 16500636592448634991421939)
      ·
        refine ⟨24750954888672952487132909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16500636592448634991421939 24750954888672952487132909)
        ·
          refine ⟨9281608083252357182674841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24750954888672952487132909 9281608083252357182674841)
          ·
            refine ⟨6961206062439267887006131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9281608083252357182674841 6961206062439267887006131)
            ·
              refine ⟨10441809093658901830509197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6961206062439267887006131 10441809093658901830509197)
              ·
                refine ⟨3915678410122088186440949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10441809093658901830509197 3915678410122088186440949)
                ·
                  refine ⟨367094850948945767478839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915678410122088186440949 367094850948945767478839)
                  ·
                    rfl

theorem cell20_804279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_804279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804279 prefixEnd_804279 := by exact prefixLift 804279
  have htrace : WordTrace (prefixWord ++ tailWord_804279) baseStart_804279 baseEnd_804279 := by
    simpa [prefixWord, tailWord_804279, baseEnd_804279] using wordTrace_append hprefix tailTrace_804279
  have hstable : (prefixWord ++ tailWord_804279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804279).length < 2 ^ (prefixWord ++ tailWord_804279).sum := by decide
  have hdescent : baseEnd_804279 < baseStart_804279 := by decide
  rcases family_descends (prefixWord ++ tailWord_804279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804292 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_804292 : Nat := 118140960795 + 804292 * 2 ^ 59
def prefixEnd_804292 : Nat := 4983230072969 + 3 ^ 40 * 804292 * 2
def baseEnd_804292 : Nat := 367100784503175500045453

theorem tailTrace_804292 : CollatzResearch.WordTrace tailWord_804292 prefixEnd_804292 367100784503175500045453 := by
  unfold tailWord_804292
  simp only [CollatzResearch.WordTrace]
  refine ⟨14667469601097460491375565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19556626134796613988500753 14667469601097460491375565)
  ·
    refine ⟨5500301100411547684265837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14667469601097460491375565 5500301100411547684265837)
    ·
      refine ⟨2062612912654330381599689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5500301100411547684265837 2062612912654330381599689)
      ·
        refine ⟨1546959684490747786199767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2062612912654330381599689 1546959684490747786199767)
        ·
          refine ⟨2320439526736121679299651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546959684490747786199767 2320439526736121679299651)
          ·
            refine ⟨3480659290104182518949477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320439526736121679299651 3480659290104182518949477)
            ·
              refine ⟨652623616894534222303027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3480659290104182518949477 652623616894534222303027)
              ·
                refine ⟨978935425341801333454541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652623616894534222303027 978935425341801333454541)
                ·
                  refine ⟨367100784503175500045453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978935425341801333454541 367100784503175500045453)
                  ·
                    rfl

theorem cell20_804292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_804292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804292 prefixEnd_804292 := by exact prefixLift 804292
  have htrace : WordTrace (prefixWord ++ tailWord_804292) baseStart_804292 baseEnd_804292 := by
    simpa [prefixWord, tailWord_804292, baseEnd_804292] using wordTrace_append hprefix tailTrace_804292
  have hstable : (prefixWord ++ tailWord_804292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804292).length < 2 ^ (prefixWord ++ tailWord_804292).sum := by decide
  have hdescent : baseEnd_804292 < baseStart_804292 := by decide
  rcases family_descends (prefixWord ++ tailWord_804292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804296 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_804296 : Nat := 118140960795 + 804296 * 2 ^ 59
def prefixEnd_804296 : Nat := 4983230072969 + 3 ^ 40 * 804296 * 2
def baseEnd_804296 : Nat := 367102610212169263912103

theorem tailTrace_804296 : CollatzResearch.WordTrace tailWord_804296 prefixEnd_804296 367102610212169263912103 := by
  unfold tailWord_804296
  simp only [CollatzResearch.WordTrace]
  refine ⟨14667542547090214832948371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19556723396120286443931161 14667542547090214832948371)
  ·
    refine ⟨22001313820635322249422557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14667542547090214832948371 22001313820635322249422557)
    ·
      refine ⟨8250492682738245843533459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22001313820635322249422557 8250492682738245843533459)
      ·
        refine ⟨12375739024107368765300189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8250492682738245843533459 12375739024107368765300189)
        ·
          refine ⟨4640902134040263286987571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12375739024107368765300189 4640902134040263286987571)
          ·
            refine ⟨6961353201060394930481357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640902134040263286987571 6961353201060394930481357)
            ·
              refine ⟨2610507450397648098930509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6961353201060394930481357 2610507450397648098930509)
              ·
                refine ⟨978940293899118037098941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2610507450397648098930509 978940293899118037098941)
                ·
                  refine ⟨367102610212169263912103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 978940293899118037098941 367102610212169263912103)
                  ·
                    rfl

theorem cell20_804296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_804296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804296 prefixEnd_804296 := by exact prefixLift 804296
  have htrace : WordTrace (prefixWord ++ tailWord_804296) baseStart_804296 baseEnd_804296 := by
    simpa [prefixWord, tailWord_804296, baseEnd_804296] using wordTrace_append hprefix tailTrace_804296
  have hstable : (prefixWord ++ tailWord_804296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804296).length < 2 ^ (prefixWord ++ tailWord_804296).sum := by decide
  have hdescent : baseEnd_804296 < baseStart_804296 := by decide
  rcases family_descends (prefixWord ++ tailWord_804296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804333 : List Nat := [1, 5, 1, 3, 2, 2, 2, 2, 2]
def baseStart_804333 : Nat := 118140960795 + 804333 * 2 ^ 59
def prefixEnd_804333 : Nat := 4983230072969 + 3 ^ 40 * 804333 * 2
def baseEnd_804333 : Nat := 367119498020361579678619

theorem tailTrace_804333 : CollatzResearch.WordTrace tailWord_804333 prefixEnd_804333 367119498020361579678619 := by
  unfold tailWord_804333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29336434595046384984993653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19557623063364256656662435 29336434595046384984993653)
  ·
    refine ⟨2750290743285598592343155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29336434595046384984993653 2750290743285598592343155)
    ·
      refine ⟨4125436114928397888514733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750290743285598592343155 4125436114928397888514733)
      ·
        refine ⟨1547038543098149208193025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4125436114928397888514733 1547038543098149208193025)
        ·
          refine ⟨1160278907323611906144769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547038543098149208193025 1160278907323611906144769)
          ·
            refine ⟨870209180492708929608577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160278907323611906144769 870209180492708929608577)
            ·
              refine ⟨652656885369531697206433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870209180492708929608577 652656885369531697206433)
              ·
                refine ⟨489492664027148772904825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652656885369531697206433 489492664027148772904825)
                ·
                  refine ⟨367119498020361579678619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489492664027148772904825 367119498020361579678619)
                  ·
                    rfl

theorem cell20_804333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_804333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804333 prefixEnd_804333 := by exact prefixLift 804333
  have htrace : WordTrace (prefixWord ++ tailWord_804333) baseStart_804333 baseEnd_804333 := by
    simpa [prefixWord, tailWord_804333, baseEnd_804333] using wordTrace_append hprefix tailTrace_804333
  have hstable : (prefixWord ++ tailWord_804333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804333).length < 2 ^ (prefixWord ++ tailWord_804333).sum := by decide
  have hdescent : baseEnd_804333 < baseStart_804333 := by decide
  rcases family_descends (prefixWord ++ tailWord_804333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804337 : List Nat := [1, 2, 2, 2, 3, 2, 4, 2, 2]
def baseStart_804337 : Nat := 118140960795 + 804337 * 2 ^ 59
def prefixEnd_804337 : Nat := 4983230072969 + 3 ^ 40 * 804337 * 2
def baseEnd_804337 : Nat := 367121323729355343545269

theorem tailTrace_804337 : CollatzResearch.WordTrace tailWord_804337 prefixEnd_804337 367121323729355343545269 := by
  unfold tailWord_804337
  simp only [CollatzResearch.WordTrace]
  refine ⟨29336580487031893668139265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19557720324687929112092843 29336580487031893668139265)
  ·
    refine ⟨22002435365273920251104449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29336580487031893668139265 22002435365273920251104449)
    ·
      refine ⟨16501826523955440188328337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22002435365273920251104449 16501826523955440188328337)
      ·
        refine ⟨12376369892966580141246253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16501826523955440188328337 12376369892966580141246253)
        ·
          refine ⟨4641138709862467552967345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12376369892966580141246253 4641138709862467552967345)
          ·
            refine ⟨3480854032396850664725509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4641138709862467552967345 3480854032396850664725509)
            ·
              refine ⟨652660131074409499636033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3480854032396850664725509 652660131074409499636033)
              ·
                refine ⟨489495098305807124727025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652660131074409499636033 489495098305807124727025)
                ·
                  refine ⟨367121323729355343545269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489495098305807124727025 367121323729355343545269)
                  ·
                    rfl

theorem cell20_804337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_804337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804337 prefixEnd_804337 := by exact prefixLift 804337
  have htrace : WordTrace (prefixWord ++ tailWord_804337) baseStart_804337 baseEnd_804337 := by
    simpa [prefixWord, tailWord_804337, baseEnd_804337] using wordTrace_append hprefix tailTrace_804337
  have hstable : (prefixWord ++ tailWord_804337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804337).length < 2 ^ (prefixWord ++ tailWord_804337).sum := by decide
  have hdescent : baseEnd_804337 < baseStart_804337 := by decide
  rcases family_descends (prefixWord ++ tailWord_804337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804348 : List Nat := [2, 2, 2, 1, 2, 1, 5, 5]
def baseStart_804348 : Nat := 118140960795 + 804348 * 2 ^ 59
def prefixEnd_804348 : Nat := 4983230072969 + 3 ^ 40 * 804348 * 2
def baseEnd_804348 : Nat := 122375448143029398059519

theorem tailTrace_804348 : CollatzResearch.WordTrace tailWord_804348 prefixEnd_804348 122375448143029398059519 := by
  unfold tailWord_804348
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668490844996021273394849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19557987793328028364526465 14668490844996021273394849)
  ·
    refine ⟨11001368133747015955046137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14668490844996021273394849 11001368133747015955046137)
    ·
      refine ⟨8251026100310261966284603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11001368133747015955046137 8251026100310261966284603)
      ·
        refine ⟨12376539150465392949426905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8251026100310261966284603 12376539150465392949426905)
        ·
          refine ⟨9282404362849044712070179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12376539150465392949426905 9282404362849044712070179)
          ·
            refine ⟨13923606544273567068105269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9282404362849044712070179 13923606544273567068105269)
            ·
              refine ⟨1305338113525646912634869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13923606544273567068105269 1305338113525646912634869)
              ·
                refine ⟨122375448143029398059519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1305338113525646912634869 122375448143029398059519)
                ·
                  rfl

theorem cell20_804348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_804348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804348 prefixEnd_804348 := by exact prefixLift 804348
  have htrace : WordTrace (prefixWord ++ tailWord_804348) baseStart_804348 baseEnd_804348 := by
    simpa [prefixWord, tailWord_804348, baseEnd_804348] using wordTrace_append hprefix tailTrace_804348
  have hstable : (prefixWord ++ tailWord_804348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804348).length < 2 ^ (prefixWord ++ tailWord_804348).sum := by decide
  have hdescent : baseEnd_804348 < baseStart_804348 := by decide
  rcases family_descends (prefixWord ++ tailWord_804348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804417 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_804417 : Nat := 118140960795 + 804417 * 2 ^ 59
def prefixEnd_804417 : Nat := 4983230072969 + 3 ^ 40 * 804417 * 2
def baseEnd_804417 : Nat := 367157837909230620878275

theorem tailTrace_804417 : CollatzResearch.WordTrace tailWord_804417 prefixEnd_804417 367157837909230620878275 := by
  unfold tailWord_804417
  simp only [CollatzResearch.WordTrace]
  refine ⟨29339498326742067331051505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19559665551161378220701003 29339498326742067331051505)
  ·
    refine ⟨22004623745056550498288629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29339498326742067331051505 22004623745056550498288629)
    ·
      refine ⟨2062933476099051609214559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22004623745056550498288629 2062933476099051609214559)
      ·
        refine ⟨3094400214148577413821839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062933476099051609214559 3094400214148577413821839)
        ·
          refine ⟨4641600321222866120732759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094400214148577413821839 4641600321222866120732759)
          ·
            refine ⟨6962400481834299181099139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4641600321222866120732759 6962400481834299181099139)
            ·
              refine ⟨10443600722751448771648709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962400481834299181099139 10443600722751448771648709)
              ·
                refine ⟨1958175135515896644684133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10443600722751448771648709 1958175135515896644684133)
                ·
                  refine ⟨367157837909230620878275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958175135515896644684133 367157837909230620878275)
                  ·
                    rfl

theorem cell20_804417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_804417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804417 prefixEnd_804417 := by exact prefixLift 804417
  have htrace : WordTrace (prefixWord ++ tailWord_804417) baseStart_804417 baseEnd_804417 := by
    simpa [prefixWord, tailWord_804417, baseEnd_804417] using wordTrace_append hprefix tailTrace_804417
  have hstable : (prefixWord ++ tailWord_804417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804417).length < 2 ^ (prefixWord ++ tailWord_804417).sum := by decide
  have hdescent : baseEnd_804417 < baseStart_804417 := by decide
  rcases family_descends (prefixWord ++ tailWord_804417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804451 : List Nat := [1, 1, 1, 5, 1, 4, 3, 2, 2]
def baseStart_804451 : Nat := 118140960795 + 804451 * 2 ^ 59
def prefixEnd_804451 : Nat := 4983230072969 + 3 ^ 40 * 804451 * 2
def baseEnd_804451 : Nat := 367173356435677613744803

theorem tailTrace_804451 : CollatzResearch.WordTrace tailWord_804451 prefixEnd_804451 367173356435677613744803 := by
  unfold tailWord_804451
  simp only [CollatzResearch.WordTrace]
  refine ⟨29340738408618891137789207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19560492272412594091859471 29340738408618891137789207)
  ·
    refine ⟨44011107612928336706683811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29340738408618891137789207 44011107612928336706683811)
    ·
      refine ⟨66016661419392505060025717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44011107612928336706683811 66016661419392505060025717)
      ·
        refine ⟨6189062008068047349377411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66016661419392505060025717 6189062008068047349377411)
        ·
          refine ⟨9283593012102071024066117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189062008068047349377411 9283593012102071024066117)
          ·
            refine ⟨1740673689769138317012397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9283593012102071024066117 1740673689769138317012397)
            ·
              refine ⟨652752633663426868879649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1740673689769138317012397 652752633663426868879649)
              ·
                refine ⟨489564475247570151659737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652752633663426868879649 489564475247570151659737)
                ·
                  refine ⟨367173356435677613744803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489564475247570151659737 367173356435677613744803)
                  ·
                    rfl

theorem cell20_804451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 2].length) (baseStart_804451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804451 prefixEnd_804451 := by exact prefixLift 804451
  have htrace : WordTrace (prefixWord ++ tailWord_804451) baseStart_804451 baseEnd_804451 := by
    simpa [prefixWord, tailWord_804451, baseEnd_804451] using wordTrace_append hprefix tailTrace_804451
  have hstable : (prefixWord ++ tailWord_804451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804451).length < 2 ^ (prefixWord ++ tailWord_804451).sum := by decide
  have hdescent : baseEnd_804451 < baseStart_804451 := by decide
  rcases family_descends (prefixWord ++ tailWord_804451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804455 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_804455 : Nat := 118140960795 + 804455 * 2 ^ 59
def prefixEnd_804455 : Nat := 4983230072969 + 3 ^ 40 * 804455 * 2
def baseEnd_804455 : Nat := 367175182144671377611453

theorem tailTrace_804455 : CollatzResearch.WordTrace tailWord_804455 prefixEnd_804455 367175182144671377611453 := by
  unfold tailWord_804455
  simp only [CollatzResearch.WordTrace]
  refine ⟨29340884300604399820934819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19560589533736266547289879 29340884300604399820934819)
  ·
    refine ⟨44011326450906599731402229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29340884300604399820934819 44011326450906599731402229)
    ·
      refine ⟨4126061854772493724818959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44011326450906599731402229 4126061854772493724818959)
      ·
        refine ⟨6189092782158740587228439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126061854772493724818959 6189092782158740587228439)
        ·
          refine ⟨9283639173238110880842659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189092782158740587228439 9283639173238110880842659)
          ·
            refine ⟨13925458759857166321263989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9283639173238110880842659 13925458759857166321263989)
            ·
              refine ⟨1305511758736609342618499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13925458759857166321263989 1305511758736609342618499)
              ·
                refine ⟨1958267638104914013927749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305511758736609342618499 1958267638104914013927749)
                ·
                  refine ⟨367175182144671377611453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958267638104914013927749 367175182144671377611453)
                  ·
                    rfl

theorem cell20_804455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_804455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804455 prefixEnd_804455 := by exact prefixLift 804455
  have htrace : WordTrace (prefixWord ++ tailWord_804455) baseStart_804455 baseEnd_804455 := by
    simpa [prefixWord, tailWord_804455, baseEnd_804455] using wordTrace_append hprefix tailTrace_804455
  have hstable : (prefixWord ++ tailWord_804455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804455).length < 2 ^ (prefixWord ++ tailWord_804455).sum := by decide
  have hdescent : baseEnd_804455 < baseStart_804455 := by decide
  rcases family_descends (prefixWord ++ tailWord_804455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804461 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 3]
def baseStart_804461 : Nat := 118140960795 + 804461 * 2 ^ 59
def prefixEnd_804461 : Nat := 4983230072969 + 3 ^ 40 * 804461 * 2
def baseEnd_804461 : Nat := 367177920708162023411429

theorem tailTrace_804461 : CollatzResearch.WordTrace tailWord_804461 prefixEnd_804461 367177920708162023411429 := by
  unfold tailWord_804461
  simp only [CollatzResearch.WordTrace]
  refine ⟨29341103138582662845653237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19560735425721775230435491 29341103138582662845653237)
  ·
    refine ⟨2750728419242124641779991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29341103138582662845653237 2750728419242124641779991)
    ·
      refine ⟨4126092628863186962669987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750728419242124641779991 4126092628863186962669987)
      ·
        refine ⟨6189138943294780444004981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126092628863186962669987 6189138943294780444004981)
        ·
          refine ⟨580231775933885666625467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6189138943294780444004981 580231775933885666625467)
          ·
            refine ⟨870347663900828499938201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580231775933885666625467 870347663900828499938201)
            ·
              refine ⟨652760747925621374953651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870347663900828499938201 652760747925621374953651)
              ·
                refine ⟨979141121888432062430477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652760747925621374953651 979141121888432062430477)
                ·
                  refine ⟨367177920708162023411429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979141121888432062430477 367177920708162023411429)
                  ·
                    rfl

theorem cell20_804461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_804461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804461 prefixEnd_804461 := by exact prefixLift 804461
  have htrace : WordTrace (prefixWord ++ tailWord_804461) baseStart_804461 baseEnd_804461 := by
    simpa [prefixWord, tailWord_804461, baseEnd_804461] using wordTrace_append hprefix tailTrace_804461
  have hstable : (prefixWord ++ tailWord_804461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804461).length < 2 ^ (prefixWord ++ tailWord_804461).sum := by decide
  have hdescent : baseEnd_804461 < baseStart_804461 := by decide
  rcases family_descends (prefixWord ++ tailWord_804461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804476 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_804476 : Nat := 118140960795 + 804476 * 2 ^ 59
def prefixEnd_804476 : Nat := 4983230072969 + 3 ^ 40 * 804476 * 2
def baseEnd_804476 : Nat := 367184767116888637911367

theorem tailTrace_804476 : CollatzResearch.WordTrace tailWord_804476 prefixEnd_804476 367184767116888637911367 := by
  unfold tailWord_804476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14670825116764160203724641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19561100155685546938299521 14670825116764160203724641)
  ·
    refine ⟨11003118837573120152793481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14670825116764160203724641 11003118837573120152793481)
    ·
      refine ⟨8252339128179840114595111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11003118837573120152793481 8252339128179840114595111)
      ·
        refine ⟨12378508692269760171892667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8252339128179840114595111 12378508692269760171892667)
        ·
          refine ⟨18567763038404640257839001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378508692269760171892667 18567763038404640257839001)
          ·
            refine ⟨13925822278803480193379251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18567763038404640257839001 13925822278803480193379251)
            ·
              refine ⟨20888733418205220290068877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13925822278803480193379251 20888733418205220290068877)
              ·
                refine ⟨7833275031826957608775829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20888733418205220290068877 7833275031826957608775829)
                ·
                  refine ⟨367184767116888637911367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7833275031826957608775829 367184767116888637911367)
                  ·
                    rfl

theorem cell20_804476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_804476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804476 prefixEnd_804476 := by exact prefixLift 804476
  have htrace : WordTrace (prefixWord ++ tailWord_804476) baseStart_804476 baseEnd_804476 := by
    simpa [prefixWord, tailWord_804476, baseEnd_804476] using wordTrace_append hprefix tailTrace_804476
  have hstable : (prefixWord ++ tailWord_804476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804476).length < 2 ^ (prefixWord ++ tailWord_804476).sum := by decide
  have hdescent : baseEnd_804476 < baseStart_804476 := by decide
  rcases family_descends (prefixWord ++ tailWord_804476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804500 : List Nat := [2, 4, 2, 2, 10]
def baseStart_804500 : Nat := 118140960795 + 804500 * 2 ^ 59
def prefixEnd_804500 : Nat := 4983230072969 + 3 ^ 40 * 804500 * 2
def baseEnd_804500 : Nat := 4533280510751249643349

theorem tailTrace_804500 : CollatzResearch.WordTrace tailWord_804500 prefixEnd_804500 4533280510751249643349 := by
  unfold tailWord_804500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14671262792720686253161477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19561683723627581670881969 14671262792720686253161477)
  ·
    refine ⟨2750861773635128672467777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14671262792720686253161477 2750861773635128672467777)
    ·
      refine ⟨2063146330226346504350833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2750861773635128672467777 2063146330226346504350833)
      ·
        refine ⟨1547359747669759878263125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2063146330226346504350833 1547359747669759878263125)
        ·
          refine ⟨4533280510751249643349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1547359747669759878263125 4533280510751249643349)
          ·
            rfl

theorem cell20_804500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 10].length) (baseStart_804500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804500 prefixEnd_804500 := by exact prefixLift 804500
  have htrace : WordTrace (prefixWord ++ tailWord_804500) baseStart_804500 baseEnd_804500 := by
    simpa [prefixWord, tailWord_804500, baseEnd_804500] using wordTrace_append hprefix tailTrace_804500
  have hstable : (prefixWord ++ tailWord_804500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804500).length < 2 ^ (prefixWord ++ tailWord_804500).sum := by decide
  have hdescent : baseEnd_804500 < baseStart_804500 := by decide
  rcases family_descends (prefixWord ++ tailWord_804500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804552 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_804552 : Nat := 118140960795 + 804552 * 2 ^ 59
def prefixEnd_804552 : Nat := 4983230072969 + 3 ^ 40 * 804552 * 2
def baseEnd_804552 : Nat := 367219455587770151377723

theorem tailTrace_804552 : CollatzResearch.WordTrace tailWord_804552 prefixEnd_804552 367219455587770151377723 := by
  unfold tailWord_804552
  simp only [CollatzResearch.WordTrace]
  refine ⟨14672211090626492693607955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19562948120835323591477273 14672211090626492693607955)
  ·
    refine ⟨22008316635939739040411933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14672211090626492693607955 22008316635939739040411933)
    ·
      refine ⟨8253118738477402140154475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22008316635939739040411933 8253118738477402140154475)
      ·
        refine ⟨12379678107716103210231713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8253118738477402140154475 12379678107716103210231713)
        ·
          refine ⟨9284758580787077407673785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12379678107716103210231713 9284758580787077407673785)
          ·
            refine ⟨6963568935590308055755339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9284758580787077407673785 6963568935590308055755339)
            ·
              refine ⟨10445353403385462083633009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963568935590308055755339 10445353403385462083633009)
              ·
                refine ⟨7834015052539096562724757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10445353403385462083633009 7834015052539096562724757)
                ·
                  refine ⟨367219455587770151377723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7834015052539096562724757 367219455587770151377723)
                  ·
                    rfl

theorem cell20_804552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_804552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804552 prefixEnd_804552 := by exact prefixLift 804552
  have htrace : WordTrace (prefixWord ++ tailWord_804552) baseStart_804552 baseEnd_804552 := by
    simpa [prefixWord, tailWord_804552, baseEnd_804552] using wordTrace_append hprefix tailTrace_804552
  have hstable : (prefixWord ++ tailWord_804552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804552).length < 2 ^ (prefixWord ++ tailWord_804552).sum := by decide
  have hdescent : baseEnd_804552 < baseStart_804552 := by decide
  rcases family_descends (prefixWord ++ tailWord_804552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804562 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_804562 : Nat := 118140960795 + 804562 * 2 ^ 59
def prefixEnd_804562 : Nat := 4983230072969 + 3 ^ 40 * 804562 * 2
def baseEnd_804562 : Nat := 367224019860254561044349

theorem tailTrace_804562 : CollatzResearch.WordTrace tailWord_804562 prefixEnd_804562 367224019860254561044349 := by
  unfold tailWord_804562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7336196727804189273769985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19563191274144504730053293 7336196727804189273769985)
  ·
    refine ⟨5502147545853141955327489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7336196727804189273769985 5502147545853141955327489)
    ·
      refine ⟨4126610659389856466495617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5502147545853141955327489 4126610659389856466495617)
      ·
        refine ⟨3094957994542392349871713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4126610659389856466495617 3094957994542392349871713)
        ·
          refine ⟨2321218495906794262403785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094957994542392349871713 2321218495906794262403785)
          ·
            refine ⟨1740913871930095696802839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2321218495906794262403785 1740913871930095696802839)
            ·
              refine ⟨2611370807895143545204259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740913871930095696802839 2611370807895143545204259)
              ·
                refine ⟨3917056211842715317806389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611370807895143545204259 3917056211842715317806389)
                ·
                  refine ⟨367224019860254561044349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3917056211842715317806389 367224019860254561044349)
                  ·
                    rfl

theorem cell20_804562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_804562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804562 prefixEnd_804562 := by exact prefixLift 804562
  have htrace : WordTrace (prefixWord ++ tailWord_804562) baseStart_804562 baseEnd_804562 := by
    simpa [prefixWord, tailWord_804562, baseEnd_804562] using wordTrace_append hprefix tailTrace_804562
  have hstable : (prefixWord ++ tailWord_804562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804562).length < 2 ^ (prefixWord ++ tailWord_804562).sum := by decide
  have hdescent : baseEnd_804562 < baseStart_804562 := by decide
  rcases family_descends (prefixWord ++ tailWord_804562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804569 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_804569 : Nat := 118140960795 + 804569 * 2 ^ 59
def prefixEnd_804569 : Nat := 4983230072969 + 3 ^ 40 * 804569 * 2
def baseEnd_804569 : Nat := 367227214850993647810987

theorem tailTrace_804569 : CollatzResearch.WordTrace tailWord_804569 prefixEnd_804569 367227214850993647810987 := by
  unfold tailWord_804569
  simp only [CollatzResearch.WordTrace]
  refine ⟨29345042222191397290584761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19563361481460931527056507 29345042222191397290584761)
  ·
    refine ⟨22008781666643547967938571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29345042222191397290584761 22008781666643547967938571)
    ·
      refine ⟨33013172499965321951907857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22008781666643547967938571 33013172499965321951907857)
      ·
        refine ⟨24759879374973991463930893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33013172499965321951907857 24759879374973991463930893)
        ·
          refine ⟨9284954765615246798974085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24759879374973991463930893 9284954765615246798974085)
          ·
            refine ⟨1740929018552858774807641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9284954765615246798974085 1740929018552858774807641)
            ·
              refine ⟨1305696763914644081105731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740929018552858774807641 1305696763914644081105731)
              ·
                refine ⟨1958545145871966121658597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305696763914644081105731 1958545145871966121658597)
                ·
                  refine ⟨367227214850993647810987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958545145871966121658597 367227214850993647810987)
                  ·
                    rfl

theorem cell20_804569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_804569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804569 prefixEnd_804569 := by exact prefixLift 804569
  have htrace : WordTrace (prefixWord ++ tailWord_804569) baseStart_804569 baseEnd_804569 := by
    simpa [prefixWord, tailWord_804569, baseEnd_804569] using wordTrace_append hprefix tailTrace_804569
  have hstable : (prefixWord ++ tailWord_804569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804569).length < 2 ^ (prefixWord ++ tailWord_804569).sum := by decide
  have hdescent : baseEnd_804569 < baseStart_804569 := by decide
  rcases family_descends (prefixWord ++ tailWord_804569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804593 : List Nat := [1, 2, 2, 2, 2, 5, 2, 4]
def baseStart_804593 : Nat := 118140960795 + 804593 * 2 ^ 59
def prefixEnd_804593 : Nat := 4983230072969 + 3 ^ 40 * 804593 * 2
def baseEnd_804593 : Nat := 122412723034985410336963

theorem tailTrace_804593 : CollatzResearch.WordTrace tailWord_804593 prefixEnd_804593 122412723034985410336963 := by
  unfold tailWord_804593
  simp only [CollatzResearch.WordTrace]
  refine ⟨29345917574104449389458433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19563945049402966259638955 29345917574104449389458433)
  ·
    refine ⟨22009438180578337042093825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29345917574104449389458433 22009438180578337042093825)
    ·
      refine ⟨16507078635433752781570369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22009438180578337042093825 16507078635433752781570369)
      ·
        refine ⟨12380308976575314586177777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16507078635433752781570369 12380308976575314586177777)
        ·
          refine ⟨9285231732431485939633333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12380308976575314586177777 9285231732431485939633333)
          ·
            refine ⟨870490474915451806840625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9285231732431485939633333 870490474915451806840625)
            ·
              refine ⟨652867856186588855130469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870490474915451806840625 652867856186588855130469)
              ·
                refine ⟨122412723034985410336963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652867856186588855130469 122412723034985410336963)
                ·
                  rfl

theorem cell20_804593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_804593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804593 prefixEnd_804593 := by exact prefixLift 804593
  have htrace : WordTrace (prefixWord ++ tailWord_804593) baseStart_804593 baseEnd_804593 := by
    simpa [prefixWord, tailWord_804593, baseEnd_804593] using wordTrace_append hprefix tailTrace_804593
  have hstable : (prefixWord ++ tailWord_804593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804593).length < 2 ^ (prefixWord ++ tailWord_804593).sum := by decide
  have hdescent : baseEnd_804593 < baseStart_804593 := by decide
  rcases family_descends (prefixWord ++ tailWord_804593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804673 : List Nat := [1, 2, 5, 12]
def baseStart_804673 : Nat := 118140960795 + 804673 * 2 ^ 59
def prefixEnd_804673 : Nat := 4983230072969 + 3 ^ 40 * 804673 * 2
def baseEnd_804673 : Nat := 1511418449731816906765

theorem tailTrace_804673 : CollatzResearch.WordTrace tailWord_804673 prefixEnd_804673 1511418449731816906765 := by
  unfold tailWord_804673
  simp only [CollatzResearch.WordTrace]
  refine ⟨29348835413814623052370673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19565890275876415368247115 29348835413814623052370673)
  ·
    refine ⟨22011626560360967289278005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29348835413814623052370673 22011626560360967289278005)
    ·
      refine ⟨2063589990033840683369813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22011626560360967289278005 2063589990033840683369813)
      ·
        refine ⟨1511418449731816906765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2063589990033840683369813 1511418449731816906765)
        ·
          rfl

theorem cell20_804673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 12].length) (baseStart_804673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804673 prefixEnd_804673 := by exact prefixLift 804673
  have htrace : WordTrace (prefixWord ++ tailWord_804673) baseStart_804673 baseEnd_804673 := by
    simpa [prefixWord, tailWord_804673, baseEnd_804673] using wordTrace_append hprefix tailTrace_804673
  have hstable : (prefixWord ++ tailWord_804673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804673).length < 2 ^ (prefixWord ++ tailWord_804673).sum := by decide
  have hdescent : baseEnd_804673 < baseStart_804673 := by decide
  rcases family_descends (prefixWord ++ tailWord_804673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804690 : List Nat := [3, 2, 2, 1, 1, 3, 3, 5]
def baseStart_804690 : Nat := 118140960795 + 804690 * 2 ^ 59
def prefixEnd_804690 : Nat := 4983230072969 + 3 ^ 40 * 804690 * 2
def baseEnd_804690 : Nat := 122427480849351668259053

theorem tailTrace_804690 : CollatzResearch.WordTrace tailWord_804690 prefixEnd_804690 122427480849351668259053 := by
  unfold tailWord_804690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337363863688258738934881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19566303636502023303826349 7337363863688258738934881)
  ·
    refine ⟨5503022897766194054201161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7337363863688258738934881 5503022897766194054201161)
    ·
      refine ⟨4127267173324645540650871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5503022897766194054201161 4127267173324645540650871)
      ·
        refine ⟨6190900759986968310976307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4127267173324645540650871 6190900759986968310976307)
        ·
          refine ⟨9286351139980452466464461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190900759986968310976307 9286351139980452466464461)
          ·
            refine ⟨3482381677492669674924173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9286351139980452466464461 3482381677492669674924173)
            ·
              refine ⟨1305893129059751128096565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3482381677492669674924173 1305893129059751128096565)
              ·
                refine ⟨122427480849351668259053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1305893129059751128096565 122427480849351668259053)
                ·
                  rfl

theorem cell20_804690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_804690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804690 prefixEnd_804690 := by exact prefixLift 804690
  have htrace : WordTrace (prefixWord ++ tailWord_804690) baseStart_804690 baseEnd_804690 := by
    simpa [prefixWord, tailWord_804690, baseEnd_804690] using wordTrace_append hprefix tailTrace_804690
  have hstable : (prefixWord ++ tailWord_804690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804690).length < 2 ^ (prefixWord ++ tailWord_804690).sum := by decide
  have hdescent : baseEnd_804690 < baseStart_804690 := by decide
  rcases family_descends (prefixWord ++ tailWord_804690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804697 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 3]
def baseStart_804697 : Nat := 118140960795 + 804697 * 2 ^ 59
def prefixEnd_804697 : Nat := 4983230072969 + 3 ^ 40 * 804697 * 2
def baseEnd_804697 : Nat := 367285637538794091543797

theorem tailTrace_804697 : CollatzResearch.WordTrace tailWord_804697 prefixEnd_804697 367285637538794091543797 := by
  unfold tailWord_804697
  simp only [CollatzResearch.WordTrace]
  refine ⟨29349710765727675151244345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19566473843818450100829563 29349710765727675151244345)
  ·
    refine ⟨22012283074295756363433259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29349710765727675151244345 22012283074295756363433259)
    ·
      refine ⟨33018424611443634545149889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22012283074295756363433259 33018424611443634545149889)
      ·
        refine ⟨24763818458582725908862417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33018424611443634545149889 24763818458582725908862417)
        ·
          refine ⟨18572863843937044431646813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24763818458582725908862417 18572863843937044431646813)
          ·
            refine ⟨6964823941476391661867555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18572863843937044431646813 6964823941476391661867555)
            ·
              refine ⟨10447235912214587492801333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964823941476391661867555 10447235912214587492801333)
              ·
                refine ⟨979428366770117577450125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10447235912214587492801333 979428366770117577450125)
                ·
                  refine ⟨367285637538794091543797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979428366770117577450125 367285637538794091543797)
                  ·
                    rfl

theorem cell20_804697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_804697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804697 prefixEnd_804697 := by exact prefixLift 804697
  have htrace : WordTrace (prefixWord ++ tailWord_804697) baseStart_804697 baseEnd_804697 := by
    simpa [prefixWord, tailWord_804697, baseEnd_804697] using wordTrace_append hprefix tailTrace_804697
  have hstable : (prefixWord ++ tailWord_804697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804697).length < 2 ^ (prefixWord ++ tailWord_804697).sum := by decide
  have hdescent : baseEnd_804697 < baseStart_804697 := by decide
  rcases family_descends (prefixWord ++ tailWord_804697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804700 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_804700 : Nat := 118140960795 + 804700 * 2 ^ 59
def prefixEnd_804700 : Nat := 4983230072969 + 3 ^ 40 * 804700 * 2
def baseEnd_804700 : Nat := 367287006820539414443785

theorem tailTrace_804700 : CollatzResearch.WordTrace tailWord_804700 prefixEnd_804700 367287006820539414443785 := by
  unfold tailWord_804700
  simp only [CollatzResearch.WordTrace]
  refine ⟨14674910092358403331801777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19566546789811204442402369 14674910092358403331801777)
  ·
    refine ⟨11006182569268802498851333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14674910092358403331801777 11006182569268802498851333)
    ·
      refine ⟨2063659231737900468534625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11006182569268802498851333 2063659231737900468534625)
      ·
        refine ⟨1547744423803425351400969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2063659231737900468534625 1547744423803425351400969)
        ·
          refine ⟨1160808317852569013550727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547744423803425351400969 1160808317852569013550727)
          ·
            refine ⟨1741212476778853520326091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160808317852569013550727 1741212476778853520326091)
            ·
              refine ⟨2611818715168280280489137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741212476778853520326091 2611818715168280280489137)
              ·
                refine ⟨1958864036376210210366853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611818715168280280489137 1958864036376210210366853)
                ·
                  refine ⟨367287006820539414443785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958864036376210210366853 367287006820539414443785)
                  ·
                    rfl

theorem cell20_804700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_804700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804700 prefixEnd_804700 := by exact prefixLift 804700
  have htrace : WordTrace (prefixWord ++ tailWord_804700) baseStart_804700 baseEnd_804700 := by
    simpa [prefixWord, tailWord_804700, baseEnd_804700] using wordTrace_append hprefix tailTrace_804700
  have hstable : (prefixWord ++ tailWord_804700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804700).length < 2 ^ (prefixWord ++ tailWord_804700).sum := by decide
  have hdescent : baseEnd_804700 < baseStart_804700 := by decide
  rcases family_descends (prefixWord ++ tailWord_804700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804704 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_804704 : Nat := 118140960795 + 804704 * 2 ^ 59
def prefixEnd_804704 : Nat := 4983230072969 + 3 ^ 40 * 804704 * 2
def baseEnd_804704 : Nat := 367288832529533178310435

theorem tailTrace_804704 : CollatzResearch.WordTrace tailWord_804704 prefixEnd_804704 367288832529533178310435 := by
  unfold tailWord_804704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14674983038351157673374583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19566644051134876897832777 14674983038351157673374583)
  ·
    refine ⟨22012474557526736510061875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14674983038351157673374583 22012474557526736510061875)
    ·
      refine ⟨33018711836290104765092813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22012474557526736510061875 33018711836290104765092813)
      ·
        refine ⟨12382016938608789286909805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33018711836290104765092813 12382016938608789286909805)
        ·
          refine ⟨4643256351978295982591177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12382016938608789286909805 4643256351978295982591177)
          ·
            refine ⟨3482442263983721986943383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4643256351978295982591177 3482442263983721986943383)
            ·
              refine ⟨5223663395975582980415075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482442263983721986943383 5223663395975582980415075)
              ·
                refine ⟨7835495093963374470622613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223663395975582980415075 7835495093963374470622613)
                ·
                  refine ⟨367288832529533178310435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7835495093963374470622613 367288832529533178310435)
                  ·
                    rfl

theorem cell20_804704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_804704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804704 prefixEnd_804704 := by exact prefixLift 804704
  have htrace : WordTrace (prefixWord ++ tailWord_804704) baseStart_804704 baseEnd_804704 := by
    simpa [prefixWord, tailWord_804704, baseEnd_804704] using wordTrace_append hprefix tailTrace_804704
  have hstable : (prefixWord ++ tailWord_804704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804704).length < 2 ^ (prefixWord ++ tailWord_804704).sum := by decide
  have hdescent : baseEnd_804704 < baseStart_804704 := by decide
  rcases family_descends (prefixWord ++ tailWord_804704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804707 : List Nat := [1, 1, 1, 5, 4, 1, 3, 4]
def baseStart_804707 : Nat := 118140960795 + 804707 * 2 ^ 59
def prefixEnd_804707 : Nat := 4983230072969 + 3 ^ 40 * 804707 * 2
def baseEnd_804707 : Nat := 122430067270426167070141

theorem tailTrace_804707 : CollatzResearch.WordTrace tailWord_804707 prefixEnd_804707 122430067270426167070141 := by
  unfold tailWord_804707
  simp only [CollatzResearch.WordTrace]
  refine ⟨29350075495691446859108375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19566716997127631239405583 29350075495691446859108375)
  ·
    refine ⟨44025113243537170288662563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29350075495691446859108375 44025113243537170288662563)
    ·
      refine ⟨66037669865305755432993845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44025113243537170288662563 66037669865305755432993845)
      ·
        refine ⟨6191031549872414571843173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66037669865305755432993845 6191031549872414571843173)
        ·
          refine ⟨1160818415601077732220595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6191031549872414571843173 1160818415601077732220595)
          ·
            refine ⟨1741227623401616598330893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160818415601077732220595 1741227623401616598330893)
            ·
              refine ⟨652960358775606224374085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1741227623401616598330893 652960358775606224374085)
              ·
                refine ⟨122430067270426167070141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652960358775606224374085 122430067270426167070141)
                ·
                  rfl

theorem cell20_804707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_804707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804707 prefixEnd_804707 := by exact prefixLift 804707
  have htrace : WordTrace (prefixWord ++ tailWord_804707) baseStart_804707 baseEnd_804707 := by
    simpa [prefixWord, tailWord_804707, baseEnd_804707] using wordTrace_append hprefix tailTrace_804707
  have hstable : (prefixWord ++ tailWord_804707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804707).length < 2 ^ (prefixWord ++ tailWord_804707).sum := by decide
  have hdescent : baseEnd_804707 < baseStart_804707 := by decide
  rcases family_descends (prefixWord ++ tailWord_804707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804758 : List Nat := [5, 3, 1, 1, 2, 2, 2, 4]
def baseStart_804758 : Nat := 118140960795 + 804758 * 2 ^ 59
def prefixEnd_804758 : Nat := 4983230072969 + 3 ^ 40 * 804758 * 2
def baseEnd_804758 : Nat := 122437826533649663503405

theorem tailTrace_804758 : CollatzResearch.WordTrace tailWord_804758 prefixEnd_804758 122437826533649663503405 := by
  unfold tailWord_804758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834495976156667660575933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19567957079004455046143285 1834495976156667660575933)
  ·
    refine ⟨687935991058750372715975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1834495976156667660575933 687935991058750372715975)
    ·
      refine ⟨1031903986588125559073963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687935991058750372715975 1031903986588125559073963)
      ·
        refine ⟨1547855979882188338610945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031903986588125559073963 1547855979882188338610945)
        ·
          refine ⟨1160891984911641253958209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547855979882188338610945 1160891984911641253958209)
          ·
            refine ⟨870668988683730940468657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160891984911641253958209 870668988683730940468657)
            ·
              refine ⟨653001741512798205351493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870668988683730940468657 653001741512798205351493)
              ·
                refine ⟨122437826533649663503405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653001741512798205351493 122437826533649663503405)
                ·
                  rfl

theorem cell20_804758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_804758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804758 prefixEnd_804758 := by exact prefixLift 804758
  have htrace : WordTrace (prefixWord ++ tailWord_804758) baseStart_804758 baseEnd_804758 := by
    simpa [prefixWord, tailWord_804758, baseEnd_804758] using wordTrace_append hprefix tailTrace_804758
  have hstable : (prefixWord ++ tailWord_804758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804758).length < 2 ^ (prefixWord ++ tailWord_804758).sum := by decide
  have hdescent : baseEnd_804758 < baseStart_804758 := by decide
  rcases family_descends (prefixWord ++ tailWord_804758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804797 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_804797 : Nat := 118140960795 + 804797 * 2 ^ 59
def prefixEnd_804797 : Nat := 4983230072969 + 3 ^ 40 * 804797 * 2
def baseEnd_804797 : Nat := 367331280263638188210055

theorem tailTrace_804797 : CollatzResearch.WordTrace tailWord_804797 prefixEnd_804797 367331280263638188210055 := by
  unfold tailWord_804797
  simp only [CollatzResearch.WordTrace]
  refine ⟨29353358065365392229884645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19568905376910261486589763 29353358065365392229884645)
  ·
    refine ⟨5503754637256011043103371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29353358065365392229884645 5503754637256011043103371)
    ·
      refine ⟨8255631955884016564655057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503754637256011043103371 8255631955884016564655057)
      ·
        refine ⟨6191723966913012423491293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8255631955884016564655057 6191723966913012423491293)
        ·
          refine ⟨2321896487592379658809235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6191723966913012423491293 2321896487592379658809235)
          ·
            refine ⟨3482844731388569488213853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321896487592379658809235 3482844731388569488213853)
            ·
              refine ⟨1306066774270713558080195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3482844731388569488213853 1306066774270713558080195)
              ·
                refine ⟨1959100161406070337120293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306066774270713558080195 1959100161406070337120293)
                ·
                  refine ⟨367331280263638188210055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1959100161406070337120293 367331280263638188210055)
                  ·
                    rfl

theorem cell20_804797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_804797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804797 prefixEnd_804797 := by exact prefixLift 804797
  have htrace : WordTrace (prefixWord ++ tailWord_804797) baseStart_804797 baseEnd_804797 := by
    simpa [prefixWord, tailWord_804797, baseEnd_804797] using wordTrace_append hprefix tailTrace_804797
  have hstable : (prefixWord ++ tailWord_804797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804797).length < 2 ^ (prefixWord ++ tailWord_804797).sum := by decide
  have hdescent : baseEnd_804797 < baseStart_804797 := by decide
  rcases family_descends (prefixWord ++ tailWord_804797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804811 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 3]
def baseStart_804811 : Nat := 118140960795 + 804811 * 2 ^ 59
def prefixEnd_804811 : Nat := 4983230072969 + 3 ^ 40 * 804811 * 2
def baseEnd_804811 : Nat := 367337670245116361743331

theorem tailTrace_804811 : CollatzResearch.WordTrace tailWord_804811 prefixEnd_804811 367337670245116361743331 := by
  unfold tailWord_804811
  simp only [CollatzResearch.WordTrace]
  refine ⟨29353868687314672620894287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19569245791543115080596191 29353868687314672620894287)
  ·
    refine ⟨44030803030972008931341431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29353868687314672620894287 44030803030972008931341431)
    ·
      refine ⟨66046204546458013397012147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44030803030972008931341431 66046204546458013397012147)
      ·
        refine ⟨99069306819687020095518221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66046204546458013397012147 99069306819687020095518221)
        ·
          refine ⟨37150990057382632535819333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99069306819687020095518221 37150990057382632535819333)
          ·
            refine ⟨6965810635759243600466125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37150990057382632535819333 6965810635759243600466125)
            ·
              refine ⟨2612178988409716350174797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6965810635759243600466125 2612178988409716350174797)
              ·
                refine ⟨979567120653643631315549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2612178988409716350174797 979567120653643631315549)
                ·
                  refine ⟨367337670245116361743331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979567120653643631315549 367337670245116361743331)
                  ·
                    rfl

theorem cell20_804811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_804811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804811 prefixEnd_804811 := by exact prefixLift 804811
  have htrace : WordTrace (prefixWord ++ tailWord_804811) baseStart_804811 baseEnd_804811 := by
    simpa [prefixWord, tailWord_804811, baseEnd_804811] using wordTrace_append hprefix tailTrace_804811
  have hstable : (prefixWord ++ tailWord_804811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804811).length < 2 ^ (prefixWord ++ tailWord_804811).sum := by decide
  have hdescent : baseEnd_804811 < baseStart_804811 := by decide
  rcases family_descends (prefixWord ++ tailWord_804811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804832 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_804832 : Nat := 118140960795 + 804832 * 2 ^ 59
def prefixEnd_804832 : Nat := 4983230072969 + 3 ^ 40 * 804832 * 2
def baseEnd_804832 : Nat := 367347255217333622043245

theorem tailTrace_804832 : CollatzResearch.WordTrace tailWord_804832 prefixEnd_804832 367347255217333622043245 := by
  unfold tailWord_804832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14677317310119296603704375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19569756413492395471605833 14677317310119296603704375)
  ·
    refine ⟨22015975965178944905556563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14677317310119296603704375 22015975965178944905556563)
    ·
      refine ⟨33023963947768417358334845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22015975965178944905556563 33023963947768417358334845)
      ·
        refine ⟨12383986480413156509375567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33023963947768417358334845 12383986480413156509375567)
        ·
          refine ⟨18575979720619734764063351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12383986480413156509375567 18575979720619734764063351)
          ·
            refine ⟨27863969580929602146095027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18575979720619734764063351 27863969580929602146095027)
            ·
              refine ⟨41795954371394403219142541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27863969580929602146095027 41795954371394403219142541)
              ·
                refine ⟨15673482889272901207178453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41795954371394403219142541 15673482889272901207178453)
                ·
                  refine ⟨367347255217333622043245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15673482889272901207178453 367347255217333622043245)
                  ·
                    rfl

theorem cell20_804832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_804832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804832 prefixEnd_804832 := by exact prefixLift 804832
  have htrace : WordTrace (prefixWord ++ tailWord_804832) baseStart_804832 baseEnd_804832 := by
    simpa [prefixWord, tailWord_804832, baseEnd_804832] using wordTrace_append hprefix tailTrace_804832
  have hstable : (prefixWord ++ tailWord_804832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804832).length < 2 ^ (prefixWord ++ tailWord_804832).sum := by decide
  have hdescent : baseEnd_804832 < baseStart_804832 := by decide
  rcases family_descends (prefixWord ++ tailWord_804832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804890 : List Nat := [3, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_804890 : Nat := 118140960795 + 804890 * 2 ^ 59
def prefixEnd_804890 : Nat := 4983230072969 + 3 ^ 40 * 804890 * 2
def baseEnd_804890 : Nat := 367373727997743198109675

theorem tailTrace_804890 : CollatzResearch.WordTrace tailWord_804890 prefixEnd_804890 367373727997743198109675 := by
  unfold tailWord_804890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339187513507117278255031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19571166702685646075346749 7339187513507117278255031)
  ·
    refine ⟨11008781270260675917382547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7339187513507117278255031 11008781270260675917382547)
    ·
      refine ⟨16513171905391013876073821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11008781270260675917382547 16513171905391013876073821)
      ·
        refine ⟨6192439464521630203527683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16513171905391013876073821 6192439464521630203527683)
        ·
          refine ⟨9288659196782445305291525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192439464521630203527683 9288659196782445305291525)
          ·
            refine ⟨1741623599396708494742161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9288659196782445305291525 1741623599396708494742161)
            ·
              refine ⟨1306217699547531371056621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1741623599396708494742161 1306217699547531371056621)
              ·
                refine ⟨489831637330324264146233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1306217699547531371056621 489831637330324264146233)
                ·
                  refine ⟨367373727997743198109675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489831637330324264146233 367373727997743198109675)
                  ·
                    rfl

theorem cell20_804890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_804890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804890 prefixEnd_804890 := by exact prefixLift 804890
  have htrace : WordTrace (prefixWord ++ tailWord_804890) baseStart_804890 baseEnd_804890 := by
    simpa [prefixWord, tailWord_804890, baseEnd_804890] using wordTrace_append hprefix tailTrace_804890
  have hstable : (prefixWord ++ tailWord_804890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804890).length < 2 ^ (prefixWord ++ tailWord_804890).sum := by decide
  have hdescent : baseEnd_804890 < baseStart_804890 := by decide
  rcases family_descends (prefixWord ++ tailWord_804890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804900 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 3]
def baseStart_804900 : Nat := 118140960795 + 804900 * 2 ^ 59
def prefixEnd_804900 : Nat := 4983230072969 + 3 ^ 40 * 804900 * 2
def baseEnd_804900 : Nat := 367378292270227607776301

theorem tailTrace_804900 : CollatzResearch.WordTrace tailWord_804900 prefixEnd_804900 367378292270227607776301 := by
  unfold tailWord_804900
  simp only [CollatzResearch.WordTrace]
  refine ⟨14678557391996120410442077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19571409855994827213922769 14678557391996120410442077)
  ·
    refine ⟨5504459021998545153915779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14678557391996120410442077 5504459021998545153915779)
    ·
      refine ⟨8256688532997817730873669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5504459021998545153915779 8256688532997817730873669)
      ·
        refine ⟨1548129099937090824538813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8256688532997817730873669 1548129099937090824538813)
        ·
          refine ⟨580548412476409059202055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1548129099937090824538813 580548412476409059202055)
          ·
            refine ⟨870822618714613588803083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580548412476409059202055 870822618714613588803083)
            ·
              refine ⟨1306233928071920383204625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870822618714613588803083 1306233928071920383204625)
              ·
                refine ⟨979675446053940287403469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306233928071920383204625 979675446053940287403469)
                ·
                  refine ⟨367378292270227607776301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979675446053940287403469 367378292270227607776301)
                  ·
                    rfl

theorem cell20_804900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_804900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804900 prefixEnd_804900 := by exact prefixLift 804900
  have htrace : WordTrace (prefixWord ++ tailWord_804900) baseStart_804900 baseEnd_804900 := by
    simpa [prefixWord, tailWord_804900, baseEnd_804900] using wordTrace_append hprefix tailTrace_804900
  have hstable : (prefixWord ++ tailWord_804900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804900).length < 2 ^ (prefixWord ++ tailWord_804900).sum := by decide
  have hdescent : baseEnd_804900 < baseStart_804900 := by decide
  rcases family_descends (prefixWord ++ tailWord_804900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804901 : List Nat := [1, 3, 1, 2, 2, 4, 7]
def baseStart_804901 : Nat := 118140960795 + 804901 * 2 ^ 59
def prefixEnd_804901 : Nat := 4983230072969 + 3 ^ 40 * 804901 * 2
def baseEnd_804901 : Nat := 40819860966386227638107

theorem tailTrace_804901 : CollatzResearch.WordTrace tailWord_804901 prefixEnd_804901 40819860966386227638107 := by
  unfold tailWord_804901
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357151256988617991670557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19571434171325745327780371 29357151256988617991670557)
  ·
    refine ⟨11008931721370731746876459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29357151256988617991670557 11008931721370731746876459)
    ·
      refine ⟨16513397582056097620314689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11008931721370731746876459 16513397582056097620314689)
      ·
        refine ⟨12385048186542073215236017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16513397582056097620314689 12385048186542073215236017)
        ·
          refine ⟨9288786139906554911427013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12385048186542073215236017 9288786139906554911427013)
          ·
            refine ⟨1741647401232479045892565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9288786139906554911427013 1741647401232479045892565)
            ·
              refine ⟨40819860966386227638107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1741647401232479045892565 40819860966386227638107)
              ·
                rfl

theorem cell20_804901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_804901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804901 prefixEnd_804901 := by exact prefixLift 804901
  have htrace : WordTrace (prefixWord ++ tailWord_804901) baseStart_804901 baseEnd_804901 := by
    simpa [prefixWord, tailWord_804901, baseEnd_804901] using wordTrace_append hprefix tailTrace_804901
  have hstable : (prefixWord ++ tailWord_804901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804901).length < 2 ^ (prefixWord ++ tailWord_804901).sum := by decide
  have hdescent : baseEnd_804901 < baseStart_804901 := by decide
  rcases family_descends (prefixWord ++ tailWord_804901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804918 : List Nat := [5, 1, 2, 1, 1, 1, 2, 7]
def baseStart_804918 : Nat := 118140960795 + 804918 * 2 ^ 59
def prefixEnd_804918 : Nat := 4983230072969 + 3 ^ 40 * 804918 * 2
def baseEnd_804918 : Nat := 122462169320233181725409

theorem tailTrace_804918 : CollatzResearch.WordTrace tailWord_804918 prefixEnd_804918 122462169320233181725409 := by
  unfold tailWord_804918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834860706120439368439963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19571847531951353263359605 1834860706120439368439963)
  ·
    refine ⟨2752291059180659052659945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1834860706120439368439963 2752291059180659052659945)
    ·
      refine ⟨2064218294385494289494959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2752291059180659052659945 2064218294385494289494959)
      ·
        refine ⟨3096327441578241434242439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064218294385494289494959 3096327441578241434242439)
        ·
          refine ⟨4644491162367362151363659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3096327441578241434242439 4644491162367362151363659)
          ·
            refine ⟨6966736743551043227045489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644491162367362151363659 6966736743551043227045489)
            ·
              refine ⟨5225052557663282420284117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6966736743551043227045489 5225052557663282420284117)
              ·
                refine ⟨122462169320233181725409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5225052557663282420284117 122462169320233181725409)
                ·
                  rfl

theorem cell20_804918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_804918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804918 prefixEnd_804918 := by exact prefixLift 804918
  have htrace : WordTrace (prefixWord ++ tailWord_804918) baseStart_804918 baseEnd_804918 := by
    simpa [prefixWord, tailWord_804918, baseEnd_804918] using wordTrace_append hprefix tailTrace_804918
  have hstable : (prefixWord ++ tailWord_804918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804918).length < 2 ^ (prefixWord ++ tailWord_804918).sum := by decide
  have hdescent : baseEnd_804918 < baseStart_804918 := by decide
  rcases family_descends (prefixWord ++ tailWord_804918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804921 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 3]
def baseStart_804921 : Nat := 118140960795 + 804921 * 2 ^ 59
def prefixEnd_804921 : Nat := 4983230072969 + 3 ^ 40 * 804921 * 2
def baseEnd_804921 : Nat := 367387877242444868076215

theorem tailTrace_804921 : CollatzResearch.WordTrace tailWord_804921 prefixEnd_804921 367387877242444868076215 := by
  unfold tailWord_804921
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357880716916161407398617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19571920477944107604932411 29357880716916161407398617)
  ·
    refine ⟨22018410537687121055548963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29357880716916161407398617 22018410537687121055548963)
    ·
      refine ⟨33027615806530681583323445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22018410537687121055548963 33027615806530681583323445)
      ·
        refine ⟨3096338981862251398436573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33027615806530681583323445 3096338981862251398436573)
        ·
          refine ⟨1161127118198344274413715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3096338981862251398436573 1161127118198344274413715)
          ·
            refine ⟨1741690677297516411620573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161127118198344274413715 1741690677297516411620573)
            ·
              refine ⟨653134003986568654357715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1741690677297516411620573 653134003986568654357715)
              ·
                refine ⟨979701005979852981536573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653134003986568654357715 979701005979852981536573)
                ·
                  refine ⟨367387877242444868076215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979701005979852981536573 367387877242444868076215)
                  ·
                    rfl

theorem cell20_804921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_804921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804921 prefixEnd_804921 := by exact prefixLift 804921
  have htrace : WordTrace (prefixWord ++ tailWord_804921) baseStart_804921 baseEnd_804921 := by
    simpa [prefixWord, tailWord_804921, baseEnd_804921] using wordTrace_append hprefix tailTrace_804921
  have hstable : (prefixWord ++ tailWord_804921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804921).length < 2 ^ (prefixWord ++ tailWord_804921).sum := by decide
  have hdescent : baseEnd_804921 < baseStart_804921 := by decide
  rcases family_descends (prefixWord ++ tailWord_804921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804956 : List Nat := [2, 2, 4, 1, 1, 4, 6]
def baseStart_804956 : Nat := 118140960795 + 804956 * 2 ^ 59
def prefixEnd_804956 : Nat := 4983230072969 + 3 ^ 40 * 804956 * 2
def baseEnd_804956 : Nat := 40822650244015589101045

theorem tailTrace_804956 : CollatzResearch.WordTrace tailWord_804956 prefixEnd_804956 40822650244015589101045 := by
  unfold tailWord_804956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14679578635894681192461361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19572771514526241589948481 14679578635894681192461361)
  ·
    refine ⟨11009683976921010894346021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14679578635894681192461361 11009683976921010894346021)
    ·
      refine ⟨2064315745672689542689879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11009683976921010894346021 2064315745672689542689879)
      ·
        refine ⟨3096473618509034314034819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064315745672689542689879 3096473618509034314034819)
        ·
          refine ⟨4644710427763551471052229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3096473618509034314034819 4644710427763551471052229)
          ·
            refine ⟨870883205205665900822293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4644710427763551471052229 870883205205665900822293)
            ·
              refine ⟨40822650244015589101045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 870883205205665900822293 40822650244015589101045)
              ·
                rfl

theorem cell20_804956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 6].length) (baseStart_804956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804956 prefixEnd_804956 := by exact prefixLift 804956
  have htrace : WordTrace (prefixWord ++ tailWord_804956) baseStart_804956 baseEnd_804956 := by
    simpa [prefixWord, tailWord_804956, baseEnd_804956] using wordTrace_append hprefix tailTrace_804956
  have hstable : (prefixWord ++ tailWord_804956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804956).length < 2 ^ (prefixWord ++ tailWord_804956).sum := by decide
  have hdescent : baseEnd_804956 < baseStart_804956 := by decide
  rcases family_descends (prefixWord ++ tailWord_804956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804962 : List Nat := [3, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_804962 : Nat := 118140960795 + 804962 * 2 ^ 59
def prefixEnd_804962 : Nat := 4983230072969 + 3 ^ 40 * 804962 * 2
def baseEnd_804962 : Nat := 367406590759630947709381

theorem tailTrace_804962 : CollatzResearch.WordTrace tailWord_804962 prefixEnd_804962 367406590759630947709381 := by
  unfold tailWord_804962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339844027441906352410285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19572917406511750273094093 7339844027441906352410285)
  ·
    refine ⟨2752441510290714882153857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7339844027441906352410285 2752441510290714882153857)
    ·
      refine ⟨2064331132718036161615393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2752441510290714882153857 2064331132718036161615393)
      ·
        refine ⟨1548248349538527121211545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2064331132718036161615393 1548248349538527121211545)
        ·
          refine ⟨1161186262153895340908659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1548248349538527121211545 1161186262153895340908659)
          ·
            refine ⟨1741779393230843011362989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161186262153895340908659 1741779393230843011362989)
            ·
              refine ⟨653167272461566129261121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1741779393230843011362989 653167272461566129261121)
              ·
                refine ⟨489875454346174596945841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653167272461566129261121 489875454346174596945841)
                ·
                  refine ⟨367406590759630947709381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489875454346174596945841 367406590759630947709381)
                  ·
                    rfl

theorem cell20_804962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_804962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804962 prefixEnd_804962 := by exact prefixLift 804962
  have htrace : WordTrace (prefixWord ++ tailWord_804962) baseStart_804962 baseEnd_804962 := by
    simpa [prefixWord, tailWord_804962, baseEnd_804962] using wordTrace_append hprefix tailTrace_804962
  have hstable : (prefixWord ++ tailWord_804962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804962).length < 2 ^ (prefixWord ++ tailWord_804962).sum := by decide
  have hdescent : baseEnd_804962 < baseStart_804962 := by decide
  rcases family_descends (prefixWord ++ tailWord_804962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804977 : List Nat := [1, 2, 2, 2, 1, 1, 6, 5]
def baseStart_804977 : Nat := 118140960795 + 804977 * 2 ^ 59
def prefixEnd_804977 : Nat := 4983230072969 + 3 ^ 40 * 804977 * 2
def baseEnd_804977 : Nat := 122471145722785854069773

theorem tailTrace_804977 : CollatzResearch.WordTrace tailWord_804977 prefixEnd_804977 122471145722785854069773 := by
  unfold tailWord_804977
  simp only [CollatzResearch.WordTrace]
  refine ⟨29359923204713282971437185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19573282136475521980958123 29359923204713282971437185)
  ·
    refine ⟨22019942403534962228577889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29359923204713282971437185 22019942403534962228577889)
    ·
      refine ⟨16514956802651221671433417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22019942403534962228577889 16514956802651221671433417)
      ·
        refine ⟨12386217601988416253575063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16514956802651221671433417 12386217601988416253575063)
        ·
          refine ⟨18579326402982624380362595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12386217601988416253575063 18579326402982624380362595)
          ·
            refine ⟨27868989604473936570543893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18579326402982624380362595 27868989604473936570543893)
            ·
              refine ⟨1306358887709715776744245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27868989604473936570543893 1306358887709715776744245)
              ·
                refine ⟨122471145722785854069773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1306358887709715776744245 122471145722785854069773)
                ·
                  rfl

theorem cell20_804977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_804977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_804977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_804977 prefixEnd_804977 := by exact prefixLift 804977
  have htrace : WordTrace (prefixWord ++ tailWord_804977) baseStart_804977 baseEnd_804977 := by
    simpa [prefixWord, tailWord_804977, baseEnd_804977] using wordTrace_append hprefix tailTrace_804977
  have hstable : (prefixWord ++ tailWord_804977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804977).length < 2 ^ (prefixWord ++ tailWord_804977).sum := by decide
  have hdescent : baseEnd_804977 < baseStart_804977 := by decide
  rcases family_descends (prefixWord ++ tailWord_804977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805015 : List Nat := [1, 1, 3, 3, 4, 8]
def baseStart_805015 : Nat := 118140960795 + 805015 * 2 ^ 59
def prefixEnd_805015 : Nat := 4983230072969 + 3 ^ 40 * 805015 * 2
def baseEnd_805015 : Nat := 13608547459399937738611

theorem tailTrace_805015 : CollatzResearch.WordTrace tailWord_805015 prefixEnd_805015 13608547459399937738611 := by
  unfold tailWord_805015
  simp only [CollatzResearch.WordTrace]
  refine ⟨29361309178575615461320499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19574206119050410307546999 29361309178575615461320499)
  ·
    refine ⟨44041963767863423191980749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29361309178575615461320499 44041963767863423191980749)
    ·
      refine ⟨16515736412948783696992781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44041963767863423191980749 16515736412948783696992781)
      ·
        refine ⟨6193401154855793886372293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16515736412948783696992781 6193401154855793886372293)
        ·
          refine ⟨1161262716535461353694805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6193401154855793886372293 1161262716535461353694805)
          ·
            refine ⟨13608547459399937738611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1161262716535461353694805 13608547459399937738611)
            ·
              rfl

theorem cell20_805015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 8].length) (baseStart_805015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805015 prefixEnd_805015 := by exact prefixLift 805015
  have htrace : WordTrace (prefixWord ++ tailWord_805015) baseStart_805015 baseEnd_805015 := by
    simpa [prefixWord, tailWord_805015, baseEnd_805015] using wordTrace_append hprefix tailTrace_805015
  have hstable : (prefixWord ++ tailWord_805015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805015).length < 2 ^ (prefixWord ++ tailWord_805015).sum := by decide
  have hdescent : baseEnd_805015 < baseStart_805015 := by decide
  rcases family_descends (prefixWord ++ tailWord_805015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805021 : List Nat := [1, 4, 2, 1, 1, 5, 2, 2, 2]
def baseStart_805021 : Nat := 118140960795 + 805021 * 2 ^ 59
def prefixEnd_805021 : Nat := 4983230072969 + 3 ^ 40 * 805021 * 2
def baseEnd_805021 : Nat := 367433519967288964742473

theorem tailTrace_805021 : CollatzResearch.WordTrace tailWord_805021 prefixEnd_805021 367433519967288964742473 := by
  unfold tailWord_805021
  simp only [CollatzResearch.WordTrace]
  refine ⟨29361528016553878486038917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19574352011035918990692611 29361528016553878486038917)
  ·
    refine ⟨5505286503103852216132297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29361528016553878486038917 5505286503103852216132297)
    ·
      refine ⟨4128964877327889162099223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5505286503103852216132297 4128964877327889162099223)
      ·
        refine ⟨6193447315991833743148835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128964877327889162099223 6193447315991833743148835)
        ·
          refine ⟨9290170973987750614723253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6193447315991833743148835 9290170973987750614723253)
          ·
            refine ⟨870953528811351620130305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9290170973987750614723253 870953528811351620130305)
            ·
              refine ⟨653215146608513715097729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870953528811351620130305 653215146608513715097729)
              ·
                refine ⟨489911359956385286323297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653215146608513715097729 489911359956385286323297)
                ·
                  refine ⟨367433519967288964742473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489911359956385286323297 367433519967288964742473)
                  ·
                    rfl

theorem cell20_805021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_805021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805021 prefixEnd_805021 := by exact prefixLift 805021
  have htrace : WordTrace (prefixWord ++ tailWord_805021) baseStart_805021 baseEnd_805021 := by
    simpa [prefixWord, tailWord_805021, baseEnd_805021] using wordTrace_append hprefix tailTrace_805021
  have hstable : (prefixWord ++ tailWord_805021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805021).length < 2 ^ (prefixWord ++ tailWord_805021).sum := by decide
  have hdescent : baseEnd_805021 < baseStart_805021 := by decide
  rcases family_descends (prefixWord ++ tailWord_805021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805067 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_805067 : Nat := 118140960795 + 805067 * 2 ^ 59
def prefixEnd_805067 : Nat := 4983230072969 + 3 ^ 40 * 805067 * 2
def baseEnd_805067 : Nat := 367454515620717249208951

theorem tailTrace_805067 : CollatzResearch.WordTrace tailWord_805067 prefixEnd_805067 367454515620717249208951 := by
  unfold tailWord_805067
  simp only [CollatzResearch.WordTrace]
  refine ⟨29363205774387228342213455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19575470516258152228142303 29363205774387228342213455)
  ·
    refine ⟨44044808661580842513320183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29363205774387228342213455 44044808661580842513320183)
    ·
      refine ⟨66067212992371263769980275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44044808661580842513320183 66067212992371263769980275)
      ·
        refine ⟨99100819488556895654970413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66067212992371263769980275 99100819488556895654970413)
        ·
          refine ⟨37162807308208835870613905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99100819488556895654970413 37162807308208835870613905)
          ·
            refine ⟨27872105481156626902960429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37162807308208835870613905 27872105481156626902960429)
            ·
              refine ⟨10452039555433735088610161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27872105481156626902960429 10452039555433735088610161)
              ·
                refine ⟨7839029666575301316457621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10452039555433735088610161 7839029666575301316457621)
                ·
                  refine ⟨367454515620717249208951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7839029666575301316457621 367454515620717249208951)
                  ·
                    rfl

theorem cell20_805067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_805067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805067 prefixEnd_805067 := by exact prefixLift 805067
  have htrace : WordTrace (prefixWord ++ tailWord_805067) baseStart_805067 baseEnd_805067 := by
    simpa [prefixWord, tailWord_805067, baseEnd_805067] using wordTrace_append hprefix tailTrace_805067
  have hstable : (prefixWord ++ tailWord_805067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805067).length < 2 ^ (prefixWord ++ tailWord_805067).sum := by decide
  have hdescent : baseEnd_805067 < baseStart_805067 := by decide
  rcases family_descends (prefixWord ++ tailWord_805067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805129 : List Nat := [1, 2, 1, 1, 3, 6, 6]
def baseStart_805129 : Nat := 118140960795 + 805129 * 2 ^ 59
def prefixEnd_805129 : Nat := 4983230072969 + 3 ^ 40 * 805129 * 2
def baseEnd_805129 : Nat := 40831423790013398793559

theorem tailTrace_805129 : CollatzResearch.WordTrace tailWord_805129 prefixEnd_805129 40831423790013398793559 := by
  unfold tailWord_805129
  simp only [CollatzResearch.WordTrace]
  refine ⟨29365467100162612930970441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19576978066775075287313627 29365467100162612930970441)
  ·
    refine ⟨22024100325121959698227831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29365467100162612930970441 22024100325121959698227831)
    ·
      refine ⟨33036150487682939547341747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22024100325121959698227831 33036150487682939547341747)
      ·
        refine ⟨49554225731524409321012621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33036150487682939547341747 49554225731524409321012621)
        ·
          refine ⟨18582834649321653495379733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49554225731524409321012621 18582834649321653495379733)
          ·
            refine ⟨871070374186952507595925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18582834649321653495379733 871070374186952507595925)
            ·
              refine ⟨40831423790013398793559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 871070374186952507595925 40831423790013398793559)
              ·
                rfl

theorem cell20_805129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 6].length) (baseStart_805129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805129 prefixEnd_805129 := by exact prefixLift 805129
  have htrace : WordTrace (prefixWord ++ tailWord_805129) baseStart_805129 baseEnd_805129 := by
    simpa [prefixWord, tailWord_805129, baseEnd_805129] using wordTrace_append hprefix tailTrace_805129
  have hstable : (prefixWord ++ tailWord_805129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805129).length < 2 ^ (prefixWord ++ tailWord_805129).sum := by decide
  have hdescent : baseEnd_805129 < baseStart_805129 := by decide
  rcases family_descends (prefixWord ++ tailWord_805129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805146 : List Nat := [3, 1, 1, 3, 4, 1, 2, 5]
def baseStart_805146 : Nat := 118140960795 + 805146 * 2 ^ 59
def prefixEnd_805146 : Nat := 4983230072969 + 3 ^ 40 * 805146 * 2
def baseEnd_805146 : Nat := 122496857791114695191765

theorem tailTrace_805146 : CollatzResearch.WordTrace tailWord_805146 prefixEnd_805146 122496857791114695191765 := by
  unfold tailWord_805146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341521785275256208584823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19577391427400683222892861 7341521785275256208584823)
  ·
    refine ⟨11012282677912884312877235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7341521785275256208584823 11012282677912884312877235)
    ·
      refine ⟨16518424016869326469315853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012282677912884312877235 16518424016869326469315853)
      ·
        refine ⟨6194409006325997425993445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16518424016869326469315853 6194409006325997425993445)
        ·
          refine ⟨1161451688686124517373771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6194409006325997425993445 1161451688686124517373771)
          ·
            refine ⟨1742177533029186776060657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161451688686124517373771 1742177533029186776060657)
            ·
              refine ⟨1306633149771890082045493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742177533029186776060657 1306633149771890082045493)
              ·
                refine ⟨122496857791114695191765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1306633149771890082045493 122496857791114695191765)
                ·
                  rfl

theorem cell20_805146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_805146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805146 prefixEnd_805146 := by exact prefixLift 805146
  have htrace : WordTrace (prefixWord ++ tailWord_805146) baseStart_805146 baseEnd_805146 := by
    simpa [prefixWord, tailWord_805146, baseEnd_805146] using wordTrace_append hprefix tailTrace_805146
  have hstable : (prefixWord ++ tailWord_805146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805146).length < 2 ^ (prefixWord ++ tailWord_805146).sum := by decide
  have hdescent : baseEnd_805146 < baseStart_805146 := by decide
  rcases family_descends (prefixWord ++ tailWord_805146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805191 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 3]
def baseStart_805191 : Nat := 118140960795 + 805191 * 2 ^ 59
def prefixEnd_805191 : Nat := 4983230072969 + 3 ^ 40 * 805191 * 2
def baseEnd_805191 : Nat := 367511112599523929075111

theorem tailTrace_805191 : CollatzResearch.WordTrace tailWord_805191 prefixEnd_805191 367511112599523929075111 := by
  unfold tailWord_805191
  simp only [CollatzResearch.WordTrace]
  refine ⟨29367728425937997519727427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19578485617291998346484951 29367728425937997519727427)
  ·
    refine ⟨44051592638906996279591141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29367728425937997519727427 44051592638906996279591141)
    ·
      refine ⟨8259673619795061802423339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44051592638906996279591141 8259673619795061802423339)
      ·
        refine ⟨12389510429692592703635009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8259673619795061802423339 12389510429692592703635009)
        ·
          refine ⟨9292132822269444527726257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12389510429692592703635009 9292132822269444527726257)
          ·
            refine ⟨6969099616702083395794693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9292132822269444527726257 6969099616702083395794693)
            ·
              refine ⟨1306706178131640636711505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6969099616702083395794693 1306706178131640636711505)
              ·
                refine ⟨980029633598730477533629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306706178131640636711505 980029633598730477533629)
                ·
                  refine ⟨367511112599523929075111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980029633598730477533629 367511112599523929075111)
                  ·
                    rfl

theorem cell20_805191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_805191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805191 prefixEnd_805191 := by exact prefixLift 805191
  have htrace : WordTrace (prefixWord ++ tailWord_805191) baseStart_805191 baseEnd_805191 := by
    simpa [prefixWord, tailWord_805191, baseEnd_805191] using wordTrace_append hprefix tailTrace_805191
  have hstable : (prefixWord ++ tailWord_805191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805191).length < 2 ^ (prefixWord ++ tailWord_805191).sum := by decide
  have hdescent : baseEnd_805191 < baseStart_805191 := by decide
  rcases family_descends (prefixWord ++ tailWord_805191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805214 : List Nat := [4, 4, 2, 1, 1, 1, 3, 4]
def baseStart_805214 : Nat := 118140960795 + 805214 * 2 ^ 59
def prefixEnd_805214 : Nat := 4983230072969 + 3 ^ 40 * 805214 * 2
def baseEnd_805214 : Nat := 122507203475412690436117

theorem tailTrace_805214 : CollatzResearch.WordTrace tailWord_805214 prefixEnd_805214 122507203475412690436117 := by
  unfold tailWord_805214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671070913106834055976837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19579044869903114965209797 3671070913106834055976837)
  ·
    refine ⟨688325796207531385495657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3671070913106834055976837 688325796207531385495657)
    ·
      refine ⟨516244347155648539121743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 688325796207531385495657 516244347155648539121743)
      ·
        refine ⟨774366520733472808682615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516244347155648539121743 774366520733472808682615)
        ·
          refine ⟨1161549781100209213023923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774366520733472808682615 1161549781100209213023923)
          ·
            refine ⟨1742324671650313819535885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161549781100209213023923 1742324671650313819535885)
            ·
              refine ⟨653371751868867682325957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742324671650313819535885 653371751868867682325957)
              ·
                refine ⟨122507203475412690436117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653371751868867682325957 122507203475412690436117)
                ·
                  rfl

theorem cell20_805214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_805214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805214 prefixEnd_805214 := by exact prefixLift 805214
  have htrace : WordTrace (prefixWord ++ tailWord_805214) baseStart_805214 baseEnd_805214 := by
    simpa [prefixWord, tailWord_805214, baseEnd_805214] using wordTrace_append hprefix tailTrace_805214
  have hstable : (prefixWord ++ tailWord_805214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805214).length < 2 ^ (prefixWord ++ tailWord_805214).sum := by decide
  have hdescent : baseEnd_805214 < baseStart_805214 := by decide
  rcases family_descends (prefixWord ++ tailWord_805214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805274 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_805274 : Nat := 118140960795 + 805274 * 2 ^ 59
def prefixEnd_805274 : Nat := 4983230072969 + 3 ^ 40 * 805274 * 2
def baseEnd_805274 : Nat := 367548996061144529308105

theorem tailTrace_805274 : CollatzResearch.WordTrace tailWord_805274 prefixEnd_805274 367548996061144529308105 := by
  unfold tailWord_805274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7342688921159325673749719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19580503789758201796665917 7342688921159325673749719)
  ·
    refine ⟨11014033381738988510624579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7342688921159325673749719 11014033381738988510624579)
    ·
      refine ⟨16521050072608482765936869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014033381738988510624579 16521050072608482765936869)
      ·
        refine ⟨3097696888614090518613163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16521050072608482765936869 3097696888614090518613163)
        ·
          refine ⟨4646545332921135777919745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097696888614090518613163 4646545332921135777919745)
          ·
            refine ⟨3484908999690851833439809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4646545332921135777919745 3484908999690851833439809)
            ·
              refine ⟨2613681749768138875079857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3484908999690851833439809 2613681749768138875079857)
              ·
                refine ⟨1960261312326104156309893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2613681749768138875079857 1960261312326104156309893)
                ·
                  refine ⟨367548996061144529308105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960261312326104156309893 367548996061144529308105)
                  ·
                    rfl

theorem cell20_805274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_805274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805274 prefixEnd_805274 := by exact prefixLift 805274
  have htrace : WordTrace (prefixWord ++ tailWord_805274) baseStart_805274 baseEnd_805274 := by
    simpa [prefixWord, tailWord_805274, baseEnd_805274] using wordTrace_append hprefix tailTrace_805274
  have hstable : (prefixWord ++ tailWord_805274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805274).length < 2 ^ (prefixWord ++ tailWord_805274).sum := by decide
  have hdescent : baseEnd_805274 < baseStart_805274 := by decide
  rcases family_descends (prefixWord ++ tailWord_805274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805277 : List Nat := [1, 4, 2, 1, 4, 2, 2, 4]
def baseStart_805277 : Nat := 118140960795 + 805277 * 2 ^ 59
def prefixEnd_805277 : Nat := 4983230072969 + 3 ^ 40 * 805277 * 2
def baseEnd_805277 : Nat := 122516788447629950736031

theorem tailTrace_805277 : CollatzResearch.WordTrace tailWord_805277 prefixEnd_805277 122516788447629950736031 := by
  unfold tailWord_805277
  simp only [CollatzResearch.WordTrace]
  refine ⟨29370865103626434207358085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19580576735750956138238723 29370865103626434207358085)
  ·
    refine ⟨5507037206929956413879641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29370865103626434207358085 5507037206929956413879641)
    ·
      refine ⟨4130277905197467310409731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5507037206929956413879641 4130277905197467310409731)
      ·
        refine ⟨6195416857796200965614597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130277905197467310409731 6195416857796200965614597)
        ·
          refine ⟨1161640660836787681052737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6195416857796200965614597 1161640660836787681052737)
          ·
            refine ⟨871230495627590760789553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1161640660836787681052737 871230495627590760789553)
            ·
              refine ⟨653422871720693070592165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871230495627590760789553 653422871720693070592165)
              ·
                refine ⟨122516788447629950736031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653422871720693070592165 122516788447629950736031)
                ·
                  rfl

theorem cell20_805277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_805277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805277 prefixEnd_805277 := by exact prefixLift 805277
  have htrace : WordTrace (prefixWord ++ tailWord_805277) baseStart_805277 baseEnd_805277 := by
    simpa [prefixWord, tailWord_805277, baseEnd_805277] using wordTrace_append hprefix tailTrace_805277
  have hstable : (prefixWord ++ tailWord_805277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805277).length < 2 ^ (prefixWord ++ tailWord_805277).sum := by decide
  have hdescent : baseEnd_805277 < baseStart_805277 := by decide
  rcases family_descends (prefixWord ++ tailWord_805277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805319 : List Nat := [1, 1, 4, 1, 1, 5, 2, 5]
def baseStart_805319 : Nat := 118140960795 + 805319 * 2 ^ 59
def prefixEnd_805319 : Nat := 4983230072969 + 3 ^ 40 * 805319 * 2
def baseEnd_805319 : Nat := 122523178429108124269307

theorem tailTrace_805319 : CollatzResearch.WordTrace tailWord_805319 prefixEnd_805319 122523178429108124269307 := by
  unfold tailWord_805319
  simp only [CollatzResearch.WordTrace]
  refine ⟨29372396969474275380387011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19581597979649516920258007 29372396969474275380387011)
  ·
    refine ⟨44058595454211413070580517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29372396969474275380387011 44058595454211413070580517)
    ·
      refine ⟨8260986647664639950733847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44058595454211413070580517 8260986647664639950733847)
      ·
        refine ⟨12391479971496959926100771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8260986647664639950733847 12391479971496959926100771)
        ·
          refine ⟨18587219957245439889151157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12391479971496959926100771 18587219957245439889151157)
          ·
            refine ⟨1742551870991759989607921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18587219957245439889151157 1742551870991759989607921)
            ·
              refine ⟨1306913903243819992205941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742551870991759989607921 1306913903243819992205941)
              ·
                refine ⟨122523178429108124269307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1306913903243819992205941 122523178429108124269307)
                ·
                  rfl

theorem cell20_805319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_805319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805319 prefixEnd_805319 := by exact prefixLift 805319
  have htrace : WordTrace (prefixWord ++ tailWord_805319) baseStart_805319 baseEnd_805319 := by
    simpa [prefixWord, tailWord_805319, baseEnd_805319] using wordTrace_append hprefix tailTrace_805319
  have hstable : (prefixWord ++ tailWord_805319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805319).length < 2 ^ (prefixWord ++ tailWord_805319).sum := by decide
  have hdescent : baseEnd_805319 < baseStart_805319 := by decide
  rcases family_descends (prefixWord ++ tailWord_805319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805357 : List Nat := [1, 5, 1, 3, 1, 9]
def baseStart_805357 : Nat := 118140960795 + 805357 * 2 ^ 59
def prefixEnd_805357 : Nat := 4983230072969 + 3 ^ 40 * 805357 * 2
def baseEnd_805357 : Nat := 13614328871213523316337

theorem tailTrace_805357 : CollatzResearch.WordTrace tailWord_805357 prefixEnd_805357 13614328871213523316337 := by
  unfold tailWord_805357
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373782943336607870270325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19582521962224405246846883 29373782943336607870270325)
  ·
    refine ⟨2753792150937806987837843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29373782943336607870270325 2753792150937806987837843)
    ·
      refine ⟨4130688226406710481756765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2753792150937806987837843 4130688226406710481756765)
      ·
        refine ⟨1549008084902516430658787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4130688226406710481756765 1549008084902516430658787)
        ·
          refine ⟨2323512127353774645988181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549008084902516430658787 2323512127353774645988181)
          ·
            refine ⟨13614328871213523316337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2323512127353774645988181 13614328871213523316337)
            ·
              rfl

theorem cell20_805357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 9].length) (baseStart_805357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805357 prefixEnd_805357 := by exact prefixLift 805357
  have htrace : WordTrace (prefixWord ++ tailWord_805357) baseStart_805357 baseEnd_805357 := by
    simpa [prefixWord, tailWord_805357, baseEnd_805357] using wordTrace_append hprefix tailTrace_805357
  have hstable : (prefixWord ++ tailWord_805357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805357).length < 2 ^ (prefixWord ++ tailWord_805357).sum := by decide
  have hdescent : baseEnd_805357 < baseStart_805357 := by decide
  rcases family_descends (prefixWord ++ tailWord_805357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805388 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_805388 : Nat := 118140960795 + 805388 * 2 ^ 59
def prefixEnd_805388 : Nat := 4983230072969 + 3 ^ 40 * 805388 * 2
def baseEnd_805388 : Nat := 367601028767466799507639

theorem tailTrace_805388 : CollatzResearch.WordTrace tailWord_805388 prefixEnd_805388 367601028767466799507639 := by
  unfold tailWord_805388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14687456803112150082324409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19583275737482866776432545 14687456803112150082324409)
  ·
    refine ⟨11015592602334112561743307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14687456803112150082324409 11015592602334112561743307)
    ·
      refine ⟨16523388903501168842614961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11015592602334112561743307 16523388903501168842614961)
      ·
        refine ⟨12392541677625876631961221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16523388903501168842614961 12392541677625876631961221)
        ·
          refine ⟨2323601564554851868492729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12392541677625876631961221 2323601564554851868492729)
          ·
            refine ⟨1742701173416138901369547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323601564554851868492729 1742701173416138901369547)
            ·
              refine ⟨2614051760124208352054321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742701173416138901369547 2614051760124208352054321)
              ·
                refine ⟨1960538820093156264040741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2614051760124208352054321 1960538820093156264040741)
                ·
                  refine ⟨367601028767466799507639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960538820093156264040741 367601028767466799507639)
                  ·
                    rfl

theorem cell20_805388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_805388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805388 prefixEnd_805388 := by exact prefixLift 805388
  have htrace : WordTrace (prefixWord ++ tailWord_805388) baseStart_805388 baseEnd_805388 := by
    simpa [prefixWord, tailWord_805388, baseEnd_805388] using wordTrace_append hprefix tailTrace_805388
  have hstable : (prefixWord ++ tailWord_805388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805388).length < 2 ^ (prefixWord ++ tailWord_805388).sum := by decide
  have hdescent : baseEnd_805388 < baseStart_805388 := by decide
  rcases family_descends (prefixWord ++ tailWord_805388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805395 : List Nat := [1, 1, 1, 2, 1, 5, 5, 4]
def baseStart_805395 : Nat := 118140960795 + 805395 * 2 ^ 59
def prefixEnd_805395 : Nat := 4983230072969 + 3 ^ 40 * 805395 * 2
def baseEnd_805395 : Nat := 122534741252735295424759

theorem tailTrace_805395 : CollatzResearch.WordTrace tailWord_805395 prefixEnd_805395 122534741252735295424759 := by
  unfold tailWord_805395
  simp only [CollatzResearch.WordTrace]
  refine ⟨29375168917198940360153639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19583445944799293573435759 29375168917198940360153639)
  ·
    refine ⟨44062753375798410540230459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29375168917198940360153639 44062753375798410540230459)
    ·
      refine ⟨66094130063697615810345689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44062753375798410540230459 66094130063697615810345689)
      ·
        refine ⟨49570597547773211857759267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66094130063697615810345689 49570597547773211857759267)
        ·
          refine ⟨74355896321659817786638901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49570597547773211857759267 74355896321659817786638901)
          ·
            refine ⟨6970865280155607917497397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74355896321659817786638901 6970865280155607917497397)
            ·
              refine ⟨653518620014588242265381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6970865280155607917497397 653518620014588242265381)
              ·
                refine ⟨122534741252735295424759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653518620014588242265381 122534741252735295424759)
                ·
                  rfl

theorem cell20_805395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_805395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805395 prefixEnd_805395 := by exact prefixLift 805395
  have htrace : WordTrace (prefixWord ++ tailWord_805395) baseStart_805395 baseEnd_805395 := by
    simpa [prefixWord, tailWord_805395, baseEnd_805395] using wordTrace_append hprefix tailTrace_805395
  have hstable : (prefixWord ++ tailWord_805395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805395).length < 2 ^ (prefixWord ++ tailWord_805395).sum := by decide
  have hdescent : baseEnd_805395 < baseStart_805395 := by decide
  rcases family_descends (prefixWord ++ tailWord_805395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805405 : List Nat := [1, 4, 2, 2, 1, 2, 1, 5, 2]
def baseStart_805405 : Nat := 118140960795 + 805405 * 2 ^ 59
def prefixEnd_805405 : Nat := 4983230072969 + 3 ^ 40 * 805405 * 2
def baseEnd_805405 : Nat := 367608788030690295940903

theorem tailTrace_805405 : CollatzResearch.WordTrace tailWord_805405 prefixEnd_805405 367608788030690295940903 := by
  unfold tailWord_805405
  simp only [CollatzResearch.WordTrace]
  refine ⟨29375533647162712068017669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19583689098108474712011779 29375533647162712068017669)
  ·
    refine ⟨5507912558843008512753313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29375533647162712068017669 5507912558843008512753313)
    ·
      refine ⟨4130934419132256384564985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5507912558843008512753313 4130934419132256384564985)
      ·
        refine ⟨3098200814349192288423739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4130934419132256384564985 3098200814349192288423739)
        ·
          refine ⟨4647301221523788432635609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098200814349192288423739 4647301221523788432635609)
          ·
            refine ⟨3485475916142841324476707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4647301221523788432635609 3485475916142841324476707)
            ·
              refine ⟨5228213874214261986715061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485475916142841324476707 5228213874214261986715061)
              ·
                refine ⟨490145050707587061254537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5228213874214261986715061 490145050707587061254537)
                ·
                  refine ⟨367608788030690295940903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490145050707587061254537 367608788030690295940903)
                  ·
                    rfl

theorem cell20_805405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_805405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805405 prefixEnd_805405 := by exact prefixLift 805405
  have htrace : WordTrace (prefixWord ++ tailWord_805405) baseStart_805405 baseEnd_805405 := by
    simpa [prefixWord, tailWord_805405, baseEnd_805405] using wordTrace_append hprefix tailTrace_805405
  have hstable : (prefixWord ++ tailWord_805405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805405).length < 2 ^ (prefixWord ++ tailWord_805405).sum := by decide
  have hdescent : baseEnd_805405 < baseStart_805405 := by decide
  rcases family_descends (prefixWord ++ tailWord_805405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805409 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_805409 : Nat := 118140960795 + 805409 * 2 ^ 59
def prefixEnd_805409 : Nat := 4983230072969 + 3 ^ 40 * 805409 * 2
def baseEnd_805409 : Nat := 367610613739684059807553

theorem tailTrace_805409 : CollatzResearch.WordTrace tailWord_805409 prefixEnd_805409 367610613739684059807553 := by
  unfold tailWord_805409
  simp only [CollatzResearch.WordTrace]
  refine ⟨29375679539148220751163281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19583786359432147167442187 29375679539148220751163281)
  ·
    refine ⟨22031759654361165563372461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29375679539148220751163281 22031759654361165563372461)
    ·
      refine ⟨8261909870385437086264673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22031759654361165563372461 8261909870385437086264673)
      ·
        refine ⟨6196432402789077814698505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8261909870385437086264673 6196432402789077814698505)
        ·
          refine ⟨4647324302091808361023879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6196432402789077814698505 4647324302091808361023879)
          ·
            refine ⟨6970986453137712541535819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647324302091808361023879 6970986453137712541535819)
            ·
              refine ⟨10456479679706568812303729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6970986453137712541535819 10456479679706568812303729)
              ·
                refine ⟨7842359759779926609227797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10456479679706568812303729 7842359759779926609227797)
                ·
                  refine ⟨367610613739684059807553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7842359759779926609227797 367610613739684059807553)
                  ·
                    rfl

theorem cell20_805409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_805409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805409 prefixEnd_805409 := by exact prefixLift 805409
  have htrace : WordTrace (prefixWord ++ tailWord_805409) baseStart_805409 baseEnd_805409 := by
    simpa [prefixWord, tailWord_805409, baseEnd_805409] using wordTrace_append hprefix tailTrace_805409
  have hstable : (prefixWord ++ tailWord_805409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805409).length < 2 ^ (prefixWord ++ tailWord_805409).sum := by decide
  have hdescent : baseEnd_805409 < baseStart_805409 := by decide
  rcases family_descends (prefixWord ++ tailWord_805409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805412 : List Nat := [2, 3, 1, 5, 1, 1, 7]
def baseStart_805412 : Nat := 118140960795 + 805412 * 2 ^ 59
def prefixEnd_805412 : Nat := 4983230072969 + 3 ^ 40 * 805412 * 2
def baseEnd_805412 : Nat := 40845775891269931411949

theorem tailTrace_805412 : CollatzResearch.WordTrace tailWord_805412 prefixEnd_805412 40845775891269931411949 := by
  unfold tailWord_805412
  simp only [CollatzResearch.WordTrace]
  refine ⟨14687894479068676131761245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19583859305424901509014993 14687894479068676131761245)
  ·
    refine ⟨5507960429650753549410467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14687894479068676131761245 5507960429650753549410467)
    ·
      refine ⟨8261940644476130324115701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5507960429650753549410467 8261940644476130324115701)
      ·
        refine ⟨774556935419637217885847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8261940644476130324115701 774556935419637217885847)
        ·
          refine ⟨1161835403129455826828771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774556935419637217885847 1161835403129455826828771)
          ·
            refine ⟨1742753104694183740243157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161835403129455826828771 1742753104694183740243157)
            ·
              refine ⟨40845775891269931411949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1742753104694183740243157 40845775891269931411949)
              ·
                rfl

theorem cell20_805412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 7].length) (baseStart_805412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805412 prefixEnd_805412 := by exact prefixLift 805412
  have htrace : WordTrace (prefixWord ++ tailWord_805412) baseStart_805412 baseEnd_805412 := by
    simpa [prefixWord, tailWord_805412, baseEnd_805412] using wordTrace_append hprefix tailTrace_805412
  have hstable : (prefixWord ++ tailWord_805412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805412).length < 2 ^ (prefixWord ++ tailWord_805412).sum := by decide
  have hdescent : baseEnd_805412 < baseStart_805412 := by decide
  rcases family_descends (prefixWord ++ tailWord_805412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805436 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_805436 : Nat := 118140960795 + 805436 * 2 ^ 59
def prefixEnd_805436 : Nat := 4983230072969 + 3 ^ 40 * 805436 * 2
def baseEnd_805436 : Nat := 367622937275391965907443

theorem tailTrace_805436 : CollatzResearch.WordTrace tailWord_805436 prefixEnd_805436 367622937275391965907443 := by
  unfold tailWord_805436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14688332155025202181198081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19584442873366936241597441 14688332155025202181198081)
  ·
    refine ⟨11016249116268901635898561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14688332155025202181198081 11016249116268901635898561)
    ·
      refine ⟨8262186837201676226923921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11016249116268901635898561 8262186837201676226923921)
      ·
        refine ⟨6196640127901257170192941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8262186837201676226923921 6196640127901257170192941)
        ·
          refine ⟨2323740047962971438822353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6196640127901257170192941 2323740047962971438822353)
          ·
            refine ⟨1742805035972228579116765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323740047962971438822353 1742805035972228579116765)
            ·
              refine ⟨653551888489585717168787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742805035972228579116765 653551888489585717168787)
              ·
                refine ⟨980327832734378575753181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653551888489585717168787 980327832734378575753181)
                ·
                  refine ⟨367622937275391965907443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980327832734378575753181 367622937275391965907443)
                  ·
                    rfl

theorem cell20_805436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_805436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805436 prefixEnd_805436 := by exact prefixLift 805436
  have htrace : WordTrace (prefixWord ++ tailWord_805436) baseStart_805436 baseEnd_805436 := by
    simpa [prefixWord, tailWord_805436, baseEnd_805436] using wordTrace_append hprefix tailTrace_805436
  have hstable : (prefixWord ++ tailWord_805436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805436).length < 2 ^ (prefixWord ++ tailWord_805436).sum := by decide
  have hdescent : baseEnd_805436 < baseStart_805436 := by decide
  rcases family_descends (prefixWord ++ tailWord_805436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805440 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_805440 : Nat := 118140960795 + 805440 * 2 ^ 59
def prefixEnd_805440 : Nat := 4983230072969 + 3 ^ 40 * 805440 * 2
def baseEnd_805440 : Nat := 367624762984385729774093

theorem tailTrace_805440 : CollatzResearch.WordTrace tailWord_805440 prefixEnd_805440 367624762984385729774093 := by
  unfold tailWord_805440
  simp only [CollatzResearch.WordTrace]
  refine ⟨14688405101017956522770887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19584540134690608697027849 14688405101017956522770887)
  ·
    refine ⟨22032607651526934784156331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14688405101017956522770887 22032607651526934784156331)
    ·
      refine ⟨33048911477290402176234497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22032607651526934784156331 33048911477290402176234497)
      ·
        refine ⟨24786683607967801632175873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33048911477290402176234497 24786683607967801632175873)
        ·
          refine ⟨18590012705975851224131905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24786683607967801632175873 18590012705975851224131905)
          ·
            refine ⟨13942509529481888418098929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18590012705975851224131905 13942509529481888418098929)
            ·
              refine ⟨10456882147111416313574197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13942509529481888418098929 10456882147111416313574197)
              ·
                refine ⟨980332701291695279397581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10456882147111416313574197 980332701291695279397581)
                ·
                  refine ⟨367624762984385729774093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980332701291695279397581 367624762984385729774093)
                  ·
                    rfl

theorem cell20_805440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_805440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805440 prefixEnd_805440 := by exact prefixLift 805440
  have htrace : WordTrace (prefixWord ++ tailWord_805440) baseStart_805440 baseEnd_805440 := by
    simpa [prefixWord, tailWord_805440, baseEnd_805440] using wordTrace_append hprefix tailTrace_805440
  have hstable : (prefixWord ++ tailWord_805440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805440).length < 2 ^ (prefixWord ++ tailWord_805440).sum := by decide
  have hdescent : baseEnd_805440 < baseStart_805440 := by decide
  rcases family_descends (prefixWord ++ tailWord_805440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805446 : List Nat := [6, 1, 1, 1, 2, 3, 2, 4]
def baseStart_805446 : Nat := 118140960795 + 805446 * 2 ^ 59
def prefixEnd_805446 : Nat := 4983230072969 + 3 ^ 40 * 805446 * 2
def baseEnd_805446 : Nat := 122542500515958791858023

theorem tailTrace_805446 : CollatzResearch.WordTrace tailWord_805446 prefixEnd_805446 122542500515958791858023 := by
  unfold tailWord_805446
  simp only [CollatzResearch.WordTrace]
  refine ⟨918032157500443002195631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19584686026676117380173461 918032157500443002195631)
  ·
    refine ⟨1377048236250664503293447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918032157500443002195631 1377048236250664503293447)
    ·
      refine ⟨2065572354375996754940171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377048236250664503293447 2065572354375996754940171)
      ·
        refine ⟨3098358531563995132410257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065572354375996754940171 3098358531563995132410257)
        ·
          refine ⟨2323768898672996349307693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3098358531563995132410257 2323768898672996349307693)
          ·
            refine ⟨871413337002373630990385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2323768898672996349307693 871413337002373630990385)
            ·
              refine ⟨653560002751780223242789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871413337002373630990385 653560002751780223242789)
              ·
                refine ⟨122542500515958791858023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653560002751780223242789 122542500515958791858023)
                ·
                  rfl

theorem cell20_805446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_805446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805446 prefixEnd_805446 := by exact prefixLift 805446
  have htrace : WordTrace (prefixWord ++ tailWord_805446) baseStart_805446 baseEnd_805446 := by
    simpa [prefixWord, tailWord_805446, baseEnd_805446] using wordTrace_append hprefix tailTrace_805446
  have hstable : (prefixWord ++ tailWord_805446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805446).length < 2 ^ (prefixWord ++ tailWord_805446).sum := by decide
  have hdescent : baseEnd_805446 < baseStart_805446 := by decide
  rcases family_descends (prefixWord ++ tailWord_805446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805450 : List Nat := [3, 1, 2, 1, 1, 6, 2, 4]
def baseStart_805450 : Nat := 118140960795 + 805450 * 2 ^ 59
def prefixEnd_805450 : Nat := 4983230072969 + 3 ^ 40 * 805450 * 2
def baseEnd_805450 : Nat := 122543109085623379813573

theorem tailTrace_805450 : CollatzResearch.WordTrace tailWord_805450 prefixEnd_805450 122543109085623379813573 := by
  unfold tailWord_805450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344293732999921188351451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19584783287999789835603869 7344293732999921188351451)
  ·
    refine ⟨11016440599499881782527177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7344293732999921188351451 11016440599499881782527177)
    ·
      refine ⟨8262330449624911336895383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11016440599499881782527177 8262330449624911336895383)
      ·
        refine ⟨12393495674437367005343075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262330449624911336895383 12393495674437367005343075)
        ·
          refine ⟨18590243511656050508014613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12393495674437367005343075 18590243511656050508014613)
          ·
            refine ⟨871417664608877367563185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18590243511656050508014613 871417664608877367563185)
            ·
              refine ⟨653563248456658025672389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871417664608877367563185 653563248456658025672389)
              ·
                refine ⟨122543109085623379813573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653563248456658025672389 122543109085623379813573)
                ·
                  rfl

theorem cell20_805450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_805450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805450 prefixEnd_805450 := by exact prefixLift 805450
  have htrace : WordTrace (prefixWord ++ tailWord_805450) baseStart_805450 baseEnd_805450 := by
    simpa [prefixWord, tailWord_805450, baseEnd_805450] using wordTrace_append hprefix tailTrace_805450
  have hstable : (prefixWord ++ tailWord_805450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805450).length < 2 ^ (prefixWord ++ tailWord_805450).sum := by decide
  have hdescent : baseEnd_805450 < baseStart_805450 := by decide
  rcases family_descends (prefixWord ++ tailWord_805450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805460 : List Nat := [2, 4, 1, 1, 1, 5, 1, 3, 2]
def baseStart_805460 : Nat := 118140960795 + 805460 * 2 ^ 59
def prefixEnd_805460 : Nat := 4983230072969 + 3 ^ 40 * 805460 * 2
def baseEnd_805460 : Nat := 367633891529354549107345

theorem tailTrace_805460 : CollatzResearch.WordTrace tailWord_805460 prefixEnd_805460 367633891529354549107345 := by
  unfold tailWord_805460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14688769830981728230634917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19585026441308970974179889 14688769830981728230634917)
  ·
    refine ⟨2754144343309074043244047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14688769830981728230634917 2754144343309074043244047)
    ·
      refine ⟨4131216514963611064866071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2754144343309074043244047 4131216514963611064866071)
      ·
        refine ⟨6196824772445416597299107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4131216514963611064866071 6196824772445416597299107)
        ·
          refine ⟨9295237158668124895948661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6196824772445416597299107 9295237158668124895948661)
          ·
            refine ⟨871428483625136708995187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9295237158668124895948661 871428483625136708995187)
            ·
              refine ⟨1307142725437705063492781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871428483625136708995187 1307142725437705063492781)
              ·
                refine ⟨490178522039139398809793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307142725437705063492781 490178522039139398809793)
                ·
                  refine ⟨367633891529354549107345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490178522039139398809793 367633891529354549107345)
                  ·
                    rfl

theorem cell20_805460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_805460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805460 prefixEnd_805460 := by exact prefixLift 805460
  have htrace : WordTrace (prefixWord ++ tailWord_805460) baseStart_805460 baseEnd_805460 := by
    simpa [prefixWord, tailWord_805460, baseEnd_805460] using wordTrace_append hprefix tailTrace_805460
  have hstable : (prefixWord ++ tailWord_805460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805460).length < 2 ^ (prefixWord ++ tailWord_805460).sum := by decide
  have hdescent : baseEnd_805460 < baseStart_805460 := by decide
  rcases family_descends (prefixWord ++ tailWord_805460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805495 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 3]
def baseStart_805495 : Nat := 118140960795 + 805495 * 2 ^ 59
def prefixEnd_805495 : Nat := 4983230072969 + 3 ^ 40 * 805495 * 2
def baseEnd_805495 : Nat := 367649866483049982940535

theorem tailTrace_805495 : CollatzResearch.WordTrace tailWord_805495 prefixEnd_805495 367649866483049982940535 := by
  unfold tailWord_805495
  simp only [CollatzResearch.WordTrace]
  refine ⟨29378816216836657438793939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19585877477891104959195959 29378816216836657438793939)
  ·
    refine ⟨44068224325254986158190909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29378816216836657438793939 44068224325254986158190909)
    ·
      refine ⟨16525584121970619809321591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44068224325254986158190909 16525584121970619809321591)
      ·
        refine ⟨24788376182955929713982387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16525584121970619809321591 24788376182955929713982387)
        ·
          refine ⟨37182564274433894570973581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788376182955929713982387 37182564274433894570973581)
          ·
            refine ⟨13943461602912710464115093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37182564274433894570973581 13943461602912710464115093)
            ·
              refine ⟨653599762636533303005395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13943461602912710464115093 653599762636533303005395)
              ·
                refine ⟨980399643954799954508093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653599762636533303005395 980399643954799954508093)
                ·
                  refine ⟨367649866483049982940535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980399643954799954508093 367649866483049982940535)
                  ·
                    rfl

theorem cell20_805495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 3].length) (baseStart_805495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805495 prefixEnd_805495 := by exact prefixLift 805495
  have htrace : WordTrace (prefixWord ++ tailWord_805495) baseStart_805495 baseEnd_805495 := by
    simpa [prefixWord, tailWord_805495, baseEnd_805495] using wordTrace_append hprefix tailTrace_805495
  have hstable : (prefixWord ++ tailWord_805495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805495).length < 2 ^ (prefixWord ++ tailWord_805495).sum := by decide
  have hdescent : baseEnd_805495 < baseStart_805495 := by decide
  rcases family_descends (prefixWord ++ tailWord_805495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805499 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_805499 : Nat := 118140960795 + 805499 * 2 ^ 59
def prefixEnd_805499 : Nat := 4983230072969 + 3 ^ 40 * 805499 * 2
def baseEnd_805499 : Nat := 367651692192043746807185

theorem tailTrace_805499 : CollatzResearch.WordTrace tailWord_805499 prefixEnd_805499 367651692192043746807185 := by
  unfold tailWord_805499
  simp only [CollatzResearch.WordTrace]
  refine ⟨29378962108822166121939551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19585974739214777414626367 29378962108822166121939551)
  ·
    refine ⟨44068443163233249182909327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29378962108822166121939551 44068443163233249182909327)
    ·
      refine ⟨66102664744849873774363991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44068443163233249182909327 66102664744849873774363991)
      ·
        refine ⟨99153997117274810661545987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66102664744849873774363991 99153997117274810661545987)
        ·
          refine ⟨148730995675912215992318981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99153997117274810661545987 148730995675912215992318981)
          ·
            refine ⟨27887061689233540498559809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148730995675912215992318981 27887061689233540498559809)
            ·
              refine ⟨20915296266925155373919857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27887061689233540498559809 20915296266925155373919857)
              ·
                refine ⟨15686472200193866530439893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20915296266925155373919857 15686472200193866530439893)
                ·
                  refine ⟨367651692192043746807185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15686472200193866530439893 367651692192043746807185)
                  ·
                    rfl

theorem cell20_805499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_805499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805499 prefixEnd_805499 := by exact prefixLift 805499
  have htrace : WordTrace (prefixWord ++ tailWord_805499) baseStart_805499 baseEnd_805499 := by
    simpa [prefixWord, tailWord_805499, baseEnd_805499] using wordTrace_append hprefix tailTrace_805499
  have hstable : (prefixWord ++ tailWord_805499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805499).length < 2 ^ (prefixWord ++ tailWord_805499).sum := by decide
  have hdescent : baseEnd_805499 < baseStart_805499 := by decide
  rcases family_descends (prefixWord ++ tailWord_805499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805543 : List Nat := [1, 1, 6, 3, 1, 2, 1, 5]
def baseStart_805543 : Nat := 118140960795 + 805543 * 2 ^ 59
def prefixEnd_805543 : Nat := 4983230072969 + 3 ^ 40 * 805543 * 2
def baseEnd_805543 : Nat := 122557258330325049780113

theorem tailTrace_805543 : CollatzResearch.WordTrace tailWord_805543 prefixEnd_805543 122557258330325049780113 := by
  unfold tailWord_805543
  simp only [CollatzResearch.WordTrace]
  refine ⟨29380566920662761636541283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19587044613775174424360855 29380566920662761636541283)
  ·
    refine ⟨44070850380994142454811925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29380566920662761636541283 44070850380994142454811925)
    ·
      refine ⟨2065821111609100427569309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44070850380994142454811925 2065821111609100427569309)
      ·
        refine ⟨774682916853412660338491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2065821111609100427569309 774682916853412660338491)
        ·
          refine ⟨1162024375280118990507737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774682916853412660338491 1162024375280118990507737)
          ·
            refine ⟨871518281460089242880803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162024375280118990507737 871518281460089242880803)
            ·
              refine ⟨1307277422190133864321205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871518281460089242880803 1307277422190133864321205)
              ·
                refine ⟨122557258330325049780113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1307277422190133864321205 122557258330325049780113)
                ·
                  rfl

theorem cell20_805543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_805543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805543 prefixEnd_805543 := by exact prefixLift 805543
  have htrace : WordTrace (prefixWord ++ tailWord_805543) baseStart_805543 baseEnd_805543 := by
    simpa [prefixWord, tailWord_805543, baseEnd_805543] using wordTrace_append hprefix tailTrace_805543
  have hstable : (prefixWord ++ tailWord_805543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805543).length < 2 ^ (prefixWord ++ tailWord_805543).sum := by decide
  have hdescent : baseEnd_805543 < baseStart_805543 := by decide
  rcases family_descends (prefixWord ++ tailWord_805543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805550 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_805550 : Nat := 118140960795 + 805550 * 2 ^ 59
def prefixEnd_805550 : Nat := 4983230072969 + 3 ^ 40 * 805550 * 2
def baseEnd_805550 : Nat := 367674969981714236106977

theorem tailTrace_805550 : CollatzResearch.WordTrace tailWord_805550 prefixEnd_805550 367674969981714236106977 := by
  unfold tailWord_805550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672602778954675229005763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19587214821091601221364069 3672602778954675229005763)
  ·
    refine ⟨5508904168432012843508645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3672602778954675229005763 5508904168432012843508645)
    ·
      refine ⟨1032919531581002408157871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5508904168432012843508645 1032919531581002408157871)
      ·
        refine ⟨1549379297371503612236807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032919531581002408157871 1549379297371503612236807)
        ·
          refine ⟨2324068946057255418355211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549379297371503612236807 2324068946057255418355211)
          ·
            refine ⟨3486103419085883127532817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324068946057255418355211 3486103419085883127532817)
            ·
              refine ⟨2614577564314412345649613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3486103419085883127532817 2614577564314412345649613)
              ·
                refine ⟨980466586617904629618605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2614577564314412345649613 980466586617904629618605)
                ·
                  refine ⟨367674969981714236106977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980466586617904629618605 367674969981714236106977)
                  ·
                    rfl

theorem cell20_805550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_805550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805550 prefixEnd_805550 := by exact prefixLift 805550
  have htrace : WordTrace (prefixWord ++ tailWord_805550) baseStart_805550 baseEnd_805550 := by
    simpa [prefixWord, tailWord_805550, baseEnd_805550] using wordTrace_append hprefix tailTrace_805550
  have hstable : (prefixWord ++ tailWord_805550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805550).length < 2 ^ (prefixWord ++ tailWord_805550).sum := by decide
  have hdescent : baseEnd_805550 < baseStart_805550 := by decide
  rcases family_descends (prefixWord ++ tailWord_805550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805592 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_805592 : Nat := 118140960795 + 805592 * 2 ^ 59
def prefixEnd_805592 : Nat := 4983230072969 + 3 ^ 40 * 805592 * 2
def baseEnd_805592 : Nat := 367694139926148756706805

theorem tailTrace_805592 : CollatzResearch.WordTrace tailWord_805592 prefixEnd_805592 367694139926148756706805 := by
  unfold tailWord_805592
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691177048742621502537515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19588236064990162003383353 14691177048742621502537515)
  ·
    refine ⟨22036765573113932253806273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14691177048742621502537515 22036765573113932253806273)
    ·
      refine ⟨16527574179835449190354705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22036765573113932253806273 16527574179835449190354705)
      ·
        refine ⟨12395680634876586892766029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16527574179835449190354705 12395680634876586892766029)
        ·
          refine ⟨4648380238078720084787261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12395680634876586892766029 4648380238078720084787261)
          ·
            refine ⟨1743142589279520031795223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4648380238078720084787261 1743142589279520031795223)
            ·
              refine ⟨2614713883919280047692835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743142589279520031795223 2614713883919280047692835)
              ·
                refine ⟨3922070825878920071539253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614713883919280047692835 3922070825878920071539253)
                ·
                  refine ⟨367694139926148756706805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922070825878920071539253 367694139926148756706805)
                  ·
                    rfl

theorem cell20_805592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_805592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805592 prefixEnd_805592 := by exact prefixLift 805592
  have htrace : WordTrace (prefixWord ++ tailWord_805592) baseStart_805592 baseEnd_805592 := by
    simpa [prefixWord, tailWord_805592, baseEnd_805592] using wordTrace_append hprefix tailTrace_805592
  have hstable : (prefixWord ++ tailWord_805592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805592).length < 2 ^ (prefixWord ++ tailWord_805592).sum := by decide
  have hdescent : baseEnd_805592 < baseStart_805592 := by decide
  rcases family_descends (prefixWord ++ tailWord_805592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805599 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_805599 : Nat := 118140960795 + 805599 * 2 ^ 59
def prefixEnd_805599 : Nat := 4983230072969 + 3 ^ 40 * 805599 * 2
def baseEnd_805599 : Nat := 367697334916887843473443

theorem tailTrace_805599 : CollatzResearch.WordTrace tailWord_805599 prefixEnd_805599 367697334916887843473443 := by
  unfold tailWord_805599
  simp only [CollatzResearch.WordTrace]
  refine ⟨29382609408459883200579851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19588406272306588800386567 29382609408459883200579851)
  ·
    refine ⟨44073914112689824800869777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29382609408459883200579851 44073914112689824800869777)
    ·
      refine ⟨33055435584517368600652333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44073914112689824800869777 33055435584517368600652333)
      ·
        refine ⟨12395788344194013225244625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33055435584517368600652333 12395788344194013225244625)
        ·
          refine ⟨9296841258145509918933469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12395788344194013225244625 9296841258145509918933469)
          ·
            refine ⟨3486315471804566219600051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9296841258145509918933469 3486315471804566219600051)
            ·
              refine ⟨5229473207706849329400077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486315471804566219600051 5229473207706849329400077)
              ·
                refine ⟨1961052452890068498525029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5229473207706849329400077 1961052452890068498525029)
                ·
                  refine ⟨367697334916887843473443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1961052452890068498525029 367697334916887843473443)
                  ·
                    rfl

theorem cell20_805599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_805599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805599 prefixEnd_805599 := by exact prefixLift 805599
  have htrace : WordTrace (prefixWord ++ tailWord_805599) baseStart_805599 baseEnd_805599 := by
    simpa [prefixWord, tailWord_805599, baseEnd_805599] using wordTrace_append hprefix tailTrace_805599
  have hstable : (prefixWord ++ tailWord_805599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805599).length < 2 ^ (prefixWord ++ tailWord_805599).sum := by decide
  have hdescent : baseEnd_805599 < baseStart_805599 := by decide
  rcases family_descends (prefixWord ++ tailWord_805599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805650 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_805650 : Nat := 118140960795 + 805650 * 2 ^ 59
def prefixEnd_805650 : Nat := 4983230072969 + 3 ^ 40 * 805650 * 2
def baseEnd_805650 : Nat := 367720612706558332773235

theorem tailTrace_805650 : CollatzResearch.WordTrace tailWord_805650 prefixEnd_805650 367720612706558332773235 := by
  unfold tailWord_805650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346117382818779727671601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19589646354183412607124269 7346117382818779727671601)
  ·
    refine ⟨5509588037114084795753701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7346117382818779727671601 5509588037114084795753701)
    ·
      refine ⟨1033047756958890899203819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5509588037114084795753701 1033047756958890899203819)
      ·
        refine ⟨1549571635438336348805729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033047756958890899203819 1549571635438336348805729)
        ·
          refine ⟨1162178726578752261604297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1549571635438336348805729 1162178726578752261604297)
          ·
            refine ⟨871634044934064196203223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162178726578752261604297 871634044934064196203223)
            ·
              refine ⟨1307451067401096294304835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871634044934064196203223 1307451067401096294304835)
              ·
                refine ⟨1961176601101644441457253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307451067401096294304835 1961176601101644441457253)
                ·
                  refine ⟨367720612706558332773235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1961176601101644441457253 367720612706558332773235)
                  ·
                    rfl

theorem cell20_805650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_805650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805650 prefixEnd_805650 := by exact prefixLift 805650
  have htrace : WordTrace (prefixWord ++ tailWord_805650) baseStart_805650 baseEnd_805650 := by
    simpa [prefixWord, tailWord_805650, baseEnd_805650] using wordTrace_append hprefix tailTrace_805650
  have hstable : (prefixWord ++ tailWord_805650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805650).length < 2 ^ (prefixWord ++ tailWord_805650).sum := by decide
  have hdescent : baseEnd_805650 < baseStart_805650 := by decide
  rcases family_descends (prefixWord ++ tailWord_805650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805651 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_805651 : Nat := 118140960795 + 805651 * 2 ^ 59
def prefixEnd_805651 : Nat := 4983230072969 + 3 ^ 40 * 805651 * 2
def baseEnd_805651 : Nat := 367721069133806773739897

theorem tailTrace_805651 : CollatzResearch.WordTrace tailWord_805651 prefixEnd_805651 367721069133806773739897 := by
  unfold tailWord_805651
  simp only [CollatzResearch.WordTrace]
  refine ⟨29384506004271496081472807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19589670669514330720981871 29384506004271496081472807)
  ·
    refine ⟨44076759006407244122209211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29384506004271496081472807 44076759006407244122209211)
    ·
      refine ⟨66115138509610866183313817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44076759006407244122209211 66115138509610866183313817)
      ·
        refine ⟨49586353882208149637485363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66115138509610866183313817 49586353882208149637485363)
        ·
          refine ⟨74379530823312224456228045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49586353882208149637485363 74379530823312224456228045)
          ·
            refine ⟨27892324058742084171085517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74379530823312224456228045 27892324058742084171085517)
            ·
              refine ⟨10459621522028281564157069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27892324058742084171085517 10459621522028281564157069)
              ·
                refine ⟨3922358070760605586558901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10459621522028281564157069 3922358070760605586558901)
                ·
                  refine ⟨367721069133806773739897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3922358070760605586558901 367721069133806773739897)
                  ·
                    rfl

theorem cell20_805651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_805651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805651 prefixEnd_805651 := by exact prefixLift 805651
  have htrace : WordTrace (prefixWord ++ tailWord_805651) baseStart_805651 baseEnd_805651 := by
    simpa [prefixWord, tailWord_805651, baseEnd_805651] using wordTrace_append hprefix tailTrace_805651
  have hstable : (prefixWord ++ tailWord_805651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805651).length < 2 ^ (prefixWord ++ tailWord_805651).sum := by decide
  have hdescent : baseEnd_805651 < baseStart_805651 := by decide
  rcases family_descends (prefixWord ++ tailWord_805651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805664 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_805664 : Nat := 118140960795 + 805664 * 2 ^ 59
def prefixEnd_805664 : Nat := 4983230072969 + 3 ^ 40 * 805664 * 2
def baseEnd_805664 : Nat := 367727002688036506306511

theorem tailTrace_805664 : CollatzResearch.WordTrace tailWord_805664 prefixEnd_805664 367727002688036506306511 := by
  unfold tailWord_805664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14692490076612199650848023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19589986768816266201130697 14692490076612199650848023)
  ·
    refine ⟨22038735114918299476272035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14692490076612199650848023 22038735114918299476272035)
    ·
      refine ⟨33058102672377449214408053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22038735114918299476272035 33058102672377449214408053)
      ·
        refine ⟨3099197125535385863850755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33058102672377449214408053 3099197125535385863850755)
        ·
          refine ⟨4648795688303078795776133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099197125535385863850755 4648795688303078795776133)
          ·
            refine ⟨871649191556827274208025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4648795688303078795776133 871649191556827274208025)
            ·
              refine ⟨653736893667620455656019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871649191556827274208025 653736893667620455656019)
              ·
                refine ⟨980605340501430683484029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653736893667620455656019 980605340501430683484029)
                ·
                  refine ⟨367727002688036506306511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980605340501430683484029 367727002688036506306511)
                  ·
                    rfl

theorem cell20_805664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_805664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805664 prefixEnd_805664 := by exact prefixLift 805664
  have htrace : WordTrace (prefixWord ++ tailWord_805664) baseStart_805664 baseEnd_805664 := by
    simpa [prefixWord, tailWord_805664, baseEnd_805664] using wordTrace_append hprefix tailTrace_805664
  have hstable : (prefixWord ++ tailWord_805664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805664).length < 2 ^ (prefixWord ++ tailWord_805664).sum := by decide
  have hdescent : baseEnd_805664 < baseStart_805664 := by decide
  rcases family_descends (prefixWord ++ tailWord_805664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805682 : List Nat := [3, 2, 1, 1, 3, 1, 1, 8]
def baseStart_805682 : Nat := 118140960795 + 805682 * 2 ^ 59
def prefixEnd_805682 : Nat := 4983230072969 + 3 ^ 40 * 805682 * 2
def baseEnd_805682 : Nat := 122578406126169481235479

theorem tailTrace_805682 : CollatzResearch.WordTrace tailWord_805682 prefixEnd_805682 122578406126169481235479 := by
  unfold tailWord_805682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346409166789797093962825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19590424444772792250567533 7346409166789797093962825)
  ·
    refine ⟨5509806875092347820472119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7346409166789797093962825 5509806875092347820472119)
    ·
      refine ⟨8264710312638521730708179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509806875092347820472119 8264710312638521730708179)
      ·
        refine ⟨12397065468957782596062269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8264710312638521730708179 12397065468957782596062269)
        ·
          refine ⟨4648899550859168473523351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12397065468957782596062269 4648899550859168473523351)
          ·
            refine ⟨6973349326288752710285027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648899550859168473523351 6973349326288752710285027)
            ·
              refine ⟨10460023989433129065427541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973349326288752710285027 10460023989433129065427541)
              ·
                refine ⟨122578406126169481235479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10460023989433129065427541 122578406126169481235479)
                ·
                  rfl

theorem cell20_805682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_805682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805682 prefixEnd_805682 := by exact prefixLift 805682
  have htrace : WordTrace (prefixWord ++ tailWord_805682) baseStart_805682 baseEnd_805682 := by
    simpa [prefixWord, tailWord_805682, baseEnd_805682] using wordTrace_append hprefix tailTrace_805682
  have hstable : (prefixWord ++ tailWord_805682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805682).length < 2 ^ (prefixWord ++ tailWord_805682).sum := by decide
  have hdescent : baseEnd_805682 < baseStart_805682 := by decide
  rcases family_descends (prefixWord ++ tailWord_805682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805692 : List Nat := [2, 2, 2, 2, 1, 1, 1, 7, 2]
def baseStart_805692 : Nat := 118140960795 + 805692 * 2 ^ 59
def prefixEnd_805692 : Nat := 4983230072969 + 3 ^ 40 * 805692 * 2
def baseEnd_805692 : Nat := 367739782650992853373063

theorem tailTrace_805692 : CollatzResearch.WordTrace tailWord_805692 prefixEnd_805692 367739782650992853373063 := by
  unfold tailWord_805692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693000698561480041857665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19590667598081973389143553 14693000698561480041857665)
  ·
    refine ⟨11019750523921110031393249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14693000698561480041857665 11019750523921110031393249)
    ·
      refine ⟨8264812892940832523544937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11019750523921110031393249 8264812892940832523544937)
      ·
        refine ⟨6198609669705624392658703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8264812892940832523544937 6198609669705624392658703)
        ·
          refine ⟨9297914504558436588988055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198609669705624392658703 9297914504558436588988055)
          ·
            refine ⟨13946871756837654883482083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297914504558436588988055 13946871756837654883482083)
            ·
              refine ⟨20920307635256482325223125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13946871756837654883482083 20920307635256482325223125)
              ·
                refine ⟨490319710201323804497417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20920307635256482325223125 490319710201323804497417)
                ·
                  refine ⟨367739782650992853373063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490319710201323804497417 367739782650992853373063)
                  ·
                    rfl

theorem cell20_805692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_805692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805692 prefixEnd_805692 := by exact prefixLift 805692
  have htrace : WordTrace (prefixWord ++ tailWord_805692) baseStart_805692 baseEnd_805692 := by
    simpa [prefixWord, tailWord_805692, baseEnd_805692] using wordTrace_append hprefix tailTrace_805692
  have hstable : (prefixWord ++ tailWord_805692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805692).length < 2 ^ (prefixWord ++ tailWord_805692).sum := by decide
  have hdescent : baseEnd_805692 < baseStart_805692 := by decide
  rcases family_descends (prefixWord ++ tailWord_805692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805716 : List Nat := [2, 4, 1, 1, 4, 2, 1, 5]
def baseStart_805716 : Nat := 118140960795 + 805716 * 2 ^ 59
def prefixEnd_805716 : Nat := 4983230072969 + 3 ^ 40 * 805716 * 2
def baseEnd_805716 : Nat := 122583578968318478857655

theorem tailTrace_805716 : CollatzResearch.WordTrace tailWord_805716 prefixEnd_805716 122583578968318478857655 := by
  unfold tailWord_805716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693438374518006091294501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19591251166024008121726001 14693438374518006091294501)
  ·
    refine ⟨2755019695222126142117719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14693438374518006091294501 2755019695222126142117719)
    ·
      refine ⟨4132529542833189213176579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2755019695222126142117719 4132529542833189213176579)
      ·
        refine ⟨6198794314249783819764869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132529542833189213176579 6198794314249783819764869)
        ·
          refine ⟨1162273933921834466205913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6198794314249783819764869 1162273933921834466205913)
          ·
            refine ⟨871705450441375849654435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162273933921834466205913 871705450441375849654435)
            ·
              refine ⟨1307558175662063774481653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871705450441375849654435 1307558175662063774481653)
              ·
                refine ⟨122583578968318478857655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1307558175662063774481653 122583578968318478857655)
                ·
                  rfl

theorem cell20_805716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_805716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805716 prefixEnd_805716 := by exact prefixLift 805716
  have htrace : WordTrace (prefixWord ++ tailWord_805716) baseStart_805716 baseEnd_805716 := by
    simpa [prefixWord, tailWord_805716, baseEnd_805716] using wordTrace_append hprefix tailTrace_805716
  have hstable : (prefixWord ++ tailWord_805716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805716).length < 2 ^ (prefixWord ++ tailWord_805716).sum := by decide
  have hdescent : baseEnd_805716 < baseStart_805716 := by decide
  rcases family_descends (prefixWord ++ tailWord_805716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805768 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_805768 : Nat := 118140960795 + 805768 * 2 ^ 59
def prefixEnd_805768 : Nat := 4983230072969 + 3 ^ 40 * 805768 * 2
def baseEnd_805768 : Nat := 367774471121874366839419

theorem tailTrace_805768 : CollatzResearch.WordTrace tailWord_805768 prefixEnd_805768 367774471121874366839419 := by
  unfold tailWord_805768
  simp only [CollatzResearch.WordTrace]
  refine ⟨14694386672423812531740979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19592515563231750042321305 14694386672423812531740979)
  ·
    refine ⟨22041580008635718797611469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14694386672423812531740979 22041580008635718797611469)
    ·
      refine ⟨8265592503238394549104301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22041580008635718797611469 8265592503238394549104301)
      ·
        refine ⟨3099597188714397955914113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8265592503238394549104301 3099597188714397955914113)
        ·
          refine ⟨2324697891535798466935585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3099597188714397955914113 2324697891535798466935585)
          ·
            refine ⟨1743523418651848850201689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324697891535798466935585 1743523418651848850201689)
            ·
              refine ⟨1307642563988886637651267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743523418651848850201689 1307642563988886637651267)
              ·
                refine ⟨1961463845983329956476901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307642563988886637651267 1961463845983329956476901)
                ·
                  refine ⟨367774471121874366839419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1961463845983329956476901 367774471121874366839419)
                  ·
                    rfl

theorem cell20_805768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_805768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805768 prefixEnd_805768 := by exact prefixLift 805768
  have htrace : WordTrace (prefixWord ++ tailWord_805768) baseStart_805768 baseEnd_805768 := by
    simpa [prefixWord, tailWord_805768, baseEnd_805768] using wordTrace_append hprefix tailTrace_805768
  have hstable : (prefixWord ++ tailWord_805768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805768).length < 2 ^ (prefixWord ++ tailWord_805768).sum := by decide
  have hdescent : baseEnd_805768 < baseStart_805768 := by decide
  rcases family_descends (prefixWord ++ tailWord_805768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805789 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_805789 : Nat := 118140960795 + 805789 * 2 ^ 59
def prefixEnd_805789 : Nat := 4983230072969 + 3 ^ 40 * 805789 * 2
def baseEnd_805789 : Nat := 367784056094091627139333

theorem tailTrace_805789 : CollatzResearch.WordTrace tailWord_805789 prefixEnd_805789 367784056094091627139333 := by
  unfold tailWord_805789
  simp only [CollatzResearch.WordTrace]
  refine ⟨29389539277771545649996421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19593026185181030433330947 29389539277771545649996421)
  ·
    refine ⟨5510538614582164809374329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29389539277771545649996421 5510538614582164809374329)
    ·
      refine ⟨4132903960936623607030747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5510538614582164809374329 4132903960936623607030747)
      ·
        refine ⟨6199355941404935410546121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132903960936623607030747 6199355941404935410546121)
        ·
          refine ⟨4649516956053701557909591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6199355941404935410546121 4649516956053701557909591)
          ·
            refine ⟨6974275434080552336864387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649516956053701557909591 6974275434080552336864387)
            ·
              refine ⟨10461413151120828505296581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6974275434080552336864387 10461413151120828505296581)
              ·
                refine ⟨1961514965835155344743109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10461413151120828505296581 1961514965835155344743109)
                ·
                  refine ⟨367784056094091627139333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1961514965835155344743109 367784056094091627139333)
                  ·
                    rfl

theorem cell20_805789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_805789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805789 prefixEnd_805789 := by exact prefixLift 805789
  have htrace : WordTrace (prefixWord ++ tailWord_805789) baseStart_805789 baseEnd_805789 := by
    simpa [prefixWord, tailWord_805789, baseEnd_805789] using wordTrace_append hprefix tailTrace_805789
  have hstable : (prefixWord ++ tailWord_805789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805789).length < 2 ^ (prefixWord ++ tailWord_805789).sum := by decide
  have hdescent : baseEnd_805789 < baseStart_805789 := by decide
  rcases family_descends (prefixWord ++ tailWord_805789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805796 : List Nat := [2, 3, 1, 2, 1, 2, 3, 6]
def baseStart_805796 : Nat := 118140960795 + 805796 * 2 ^ 59
def prefixEnd_805796 : Nat := 4983230072969 + 3 ^ 40 * 805796 * 2
def baseEnd_805796 : Nat := 122595750361610237968657

theorem tailTrace_805796 : CollatzResearch.WordTrace tailWord_805796 prefixEnd_805796 122595750361610237968657 := by
  unfold tailWord_805796
  simp only [CollatzResearch.WordTrace]
  refine ⟨14694897294373092922750621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19593196392497457230334161 14694897294373092922750621)
  ·
    refine ⟨5510586485389909846031483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14694897294373092922750621 5510586485389909846031483)
    ·
      refine ⟨8265879728084864769047225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510586485389909846031483 8265879728084864769047225)
      ·
        refine ⟨6199409796063648576785419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8265879728084864769047225 6199409796063648576785419)
        ·
          refine ⟨9299114694095472865178129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199409796063648576785419 9299114694095472865178129)
          ·
            refine ⟨6974336020571604648883597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9299114694095472865178129 6974336020571604648883597)
            ·
              refine ⟨2615376007714351743331349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6974336020571604648883597 2615376007714351743331349)
              ·
                refine ⟨122595750361610237968657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2615376007714351743331349 122595750361610237968657)
                ·
                  rfl

theorem cell20_805796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_805796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805796 prefixEnd_805796 := by exact prefixLift 805796
  have htrace : WordTrace (prefixWord ++ tailWord_805796) baseStart_805796 baseEnd_805796 := by
    simpa [prefixWord, tailWord_805796, baseEnd_805796] using wordTrace_append hprefix tailTrace_805796
  have hstable : (prefixWord ++ tailWord_805796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805796).length < 2 ^ (prefixWord ++ tailWord_805796).sum := by decide
  have hdescent : baseEnd_805796 < baseStart_805796 := by decide
  rcases family_descends (prefixWord ++ tailWord_805796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805874 : List Nat := [3, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_805874 : Nat := 118140960795 + 805874 * 2 ^ 59
def prefixEnd_805874 : Nat := 4983230072969 + 3 ^ 40 * 805874 * 2
def baseEnd_805874 : Nat := 367822852410209109305653

theorem tailTrace_805874 : CollatzResearch.WordTrace tailWord_805874 prefixEnd_805874 367822852410209109305653 := by
  unfold tailWord_805874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348159870615901291710169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19595092988309070111227117 7348159870615901291710169)
  ·
    refine ⟨5511119902961925968782627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7348159870615901291710169 5511119902961925968782627)
    ·
      refine ⟨8266679854442888953173941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5511119902961925968782627 8266679854442888953173941)
      ·
        refine ⟨775001236354020839360057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8266679854442888953173941 775001236354020839360057)
        ·
          refine ⟨581250927265515629520043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775001236354020839360057 581250927265515629520043)
          ·
            refine ⟨871876390898273444280065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581250927265515629520043 871876390898273444280065)
            ·
              refine ⟨653907293173705083210049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871876390898273444280065 653907293173705083210049)
              ·
                refine ⟨490430469880278812407537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653907293173705083210049 490430469880278812407537)
                ·
                  refine ⟨367822852410209109305653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490430469880278812407537 367822852410209109305653)
                  ·
                    rfl

theorem cell20_805874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_805874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805874 prefixEnd_805874 := by exact prefixLift 805874
  have htrace : WordTrace (prefixWord ++ tailWord_805874) baseStart_805874 baseEnd_805874 := by
    simpa [prefixWord, tailWord_805874, baseEnd_805874] using wordTrace_append hprefix tailTrace_805874
  have hstable : (prefixWord ++ tailWord_805874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805874).length < 2 ^ (prefixWord ++ tailWord_805874).sum := by decide
  have hdescent : baseEnd_805874 < baseStart_805874 := by decide
  rcases family_descends (prefixWord ++ tailWord_805874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805878 : List Nat := [5, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_805878 : Nat := 118140960795 + 805878 * 2 ^ 59
def prefixEnd_805878 : Nat := 4983230072969 + 3 ^ 40 * 805878 * 2
def baseEnd_805878 : Nat := 367824678119202873172303

theorem tailTrace_805878 : CollatzResearch.WordTrace tailWord_805878 prefixEnd_805878 367824678119202873172303 := by
  unfold tailWord_805878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1837049085903069615624143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19595190249632742566657525 1837049085903069615624143)
  ·
    refine ⟨2755573628854604423436215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1837049085903069615624143 2755573628854604423436215)
    ·
      refine ⟨4133360443281906635154323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2755573628854604423436215 4133360443281906635154323)
      ·
        refine ⟨6200040664922859952731485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133360443281906635154323 6200040664922859952731485)
        ·
          refine ⟨2325015249346072482274307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6200040664922859952731485 2325015249346072482274307)
          ·
            refine ⟨3487522874019108723411461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325015249346072482274307 3487522874019108723411461)
            ·
              refine ⟨653910538878582885639649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3487522874019108723411461 653910538878582885639649)
              ·
                refine ⟨490432904158937164229737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653910538878582885639649 490432904158937164229737)
                ·
                  refine ⟨367824678119202873172303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490432904158937164229737 367824678119202873172303)
                  ·
                    rfl

theorem cell20_805878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_805878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805878 prefixEnd_805878 := by exact prefixLift 805878
  have htrace : WordTrace (prefixWord ++ tailWord_805878) baseStart_805878 baseEnd_805878 := by
    simpa [prefixWord, tailWord_805878, baseEnd_805878] using wordTrace_append hprefix tailTrace_805878
  have hstable : (prefixWord ++ tailWord_805878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805878).length < 2 ^ (prefixWord ++ tailWord_805878).sum := by decide
  have hdescent : baseEnd_805878 < baseStart_805878 := by decide
  rcases family_descends (prefixWord ++ tailWord_805878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805889 : List Nat := [1, 2, 4, 1, 2, 4, 1, 5]
def baseStart_805889 : Nat := 118140960795 + 805889 * 2 ^ 59
def prefixEnd_805889 : Nat := 4983230072969 + 3 ^ 40 * 805889 * 2
def baseEnd_805889 : Nat := 122609899606311907935197

theorem tailTrace_805889 : CollatzResearch.WordTrace tailWord_805889 prefixEnd_805889 122609899606311907935197 := by
  unfold tailWord_805889
  simp only [CollatzResearch.WordTrace]
  refine ⟨29393186577409262728636721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19595457718272841819091147 29393186577409262728636721)
  ·
    refine ⟨22044889933056947046477541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29393186577409262728636721 22044889933056947046477541)
    ·
      refine ⟨4133416862448177571214539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22044889933056947046477541 4133416862448177571214539)
      ·
        refine ⟨6200125293672266356821809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133416862448177571214539 6200125293672266356821809)
        ·
          refine ⟨4650093970254199767616357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6200125293672266356821809 4650093970254199767616357)
          ·
            refine ⟨871892619422662456428067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4650093970254199767616357 871892619422662456428067)
            ·
              refine ⟨1307838929133993684642101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871892619422662456428067 1307838929133993684642101)
              ·
                refine ⟨122609899606311907935197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1307838929133993684642101 122609899606311907935197)
                ·
                  rfl

theorem cell20_805889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_805889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805889 prefixEnd_805889 := by exact prefixLift 805889
  have htrace : WordTrace (prefixWord ++ tailWord_805889) baseStart_805889 baseEnd_805889 := by
    simpa [prefixWord, tailWord_805889, baseEnd_805889] using wordTrace_append hprefix tailTrace_805889
  have hstable : (prefixWord ++ tailWord_805889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805889).length < 2 ^ (prefixWord ++ tailWord_805889).sum := by decide
  have hdescent : baseEnd_805889 < baseStart_805889 := by decide
  rcases family_descends (prefixWord ++ tailWord_805889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805896 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_805896 : Nat := 118140960795 + 805896 * 2 ^ 59
def prefixEnd_805896 : Nat := 4983230072969 + 3 ^ 40 * 805896 * 2
def baseEnd_805896 : Nat := 367832893809674810572229

theorem tailTrace_805896 : CollatzResearch.WordTrace tailWord_805896 prefixEnd_805896 367832893809674810572229 := by
  unfold tailWord_805896
  simp only [CollatzResearch.WordTrace]
  refine ⟨14696720944191951462070771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19595627925589268616094361 14696720944191951462070771)
  ·
    refine ⟨22045081416287927193106157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14696720944191951462070771 22045081416287927193106157)
    ·
      refine ⟨8266905531107972697414809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22045081416287927193106157 8266905531107972697414809)
      ·
        refine ⟨6200179148330979523061107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8266905531107972697414809 6200179148330979523061107)
        ·
          refine ⟨9300268722496469284591661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200179148330979523061107 9300268722496469284591661)
          ·
            refine ⟨3487600770936175981721873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9300268722496469284591661 3487600770936175981721873)
            ·
              refine ⟨2615700578202131986291405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487600770936175981721873 2615700578202131986291405)
              ·
                refine ⟨980887716825799494859277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2615700578202131986291405 980887716825799494859277)
                ·
                  refine ⟨367832893809674810572229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980887716825799494859277 367832893809674810572229)
                  ·
                    rfl

theorem cell20_805896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_805896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805896 prefixEnd_805896 := by exact prefixLift 805896
  have htrace : WordTrace (prefixWord ++ tailWord_805896) baseStart_805896 baseEnd_805896 := by
    simpa [prefixWord, tailWord_805896, baseEnd_805896] using wordTrace_append hprefix tailTrace_805896
  have hstable : (prefixWord ++ tailWord_805896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805896).length < 2 ^ (prefixWord ++ tailWord_805896).sum := by decide
  have hdescent : baseEnd_805896 < baseStart_805896 := by decide
  rcases family_descends (prefixWord ++ tailWord_805896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805927 : List Nat := [1, 1, 7, 1, 1, 2, 7]
def baseStart_805927 : Nat := 118140960795 + 805927 * 2 ^ 59
def prefixEnd_805927 : Nat := 4983230072969 + 3 ^ 40 * 805927 * 2
def baseEnd_805927 : Nat := 40871893672708497837641

theorem tailTrace_805927 : CollatzResearch.WordTrace tailWord_805927 prefixEnd_805927 40871893672708497837641 := by
  unfold tailWord_805927
  simp only [CollatzResearch.WordTrace]
  refine ⟨29394572551271595218520035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19596381700847730145680023 29394572551271595218520035)
  ·
    refine ⟨44091858826907392827780053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29394572551271595218520035 44091858826907392827780053)
    ·
      refine ⟨1033402941255642019401095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44091858826907392827780053 1033402941255642019401095)
      ·
        refine ⟨1550104411883463029101643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033402941255642019401095 1550104411883463029101643)
        ·
          refine ⟨2325156617825194543652465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550104411883463029101643 2325156617825194543652465)
          ·
            refine ⟨1743867463368895907739349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325156617825194543652465 1743867463368895907739349)
            ·
              refine ⟨40871893672708497837641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1743867463368895907739349 40871893672708497837641)
              ·
                rfl

theorem cell20_805927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 7].length) (baseStart_805927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805927 prefixEnd_805927 := by exact prefixLift 805927
  have htrace : WordTrace (prefixWord ++ tailWord_805927) baseStart_805927 baseEnd_805927 := by
    simpa [prefixWord, tailWord_805927, baseEnd_805927] using wordTrace_append hprefix tailTrace_805927
  have hstable : (prefixWord ++ tailWord_805927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805927).length < 2 ^ (prefixWord ++ tailWord_805927).sum := by decide
  have hdescent : baseEnd_805927 < baseStart_805927 := by decide
  rcases family_descends (prefixWord ++ tailWord_805927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805930 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_805930 : Nat := 118140960795 + 805930 * 2 ^ 59
def prefixEnd_805930 : Nat := 4983230072969 + 3 ^ 40 * 805930 * 2
def baseEnd_805930 : Nat := 367848412336121803438757

theorem tailTrace_805930 : CollatzResearch.WordTrace tailWord_805930 prefixEnd_805930 367848412336121803438757 := by
  unfold tailWord_805930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348670492565181682719811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19596454646840484487252829 7348670492565181682719811)
  ·
    refine ⟨11023005738847772524079717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7348670492565181682719811 11023005738847772524079717)
    ·
      refine ⟨2066813576033957348264947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11023005738847772524079717 2066813576033957348264947)
      ·
        refine ⟨3100220364050936022397421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066813576033957348264947 3100220364050936022397421)
        ·
          refine ⟨1162582636519101008399033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3100220364050936022397421 1162582636519101008399033)
          ·
            refine ⟨871936977389325756299275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162582636519101008399033 871936977389325756299275)
            ·
              refine ⟨1307905466083988634448913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871936977389325756299275 1307905466083988634448913)
              ·
                refine ⟨980929099562991475836685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307905466083988634448913 980929099562991475836685)
                ·
                  refine ⟨367848412336121803438757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 980929099562991475836685 367848412336121803438757)
                  ·
                    rfl

theorem cell20_805930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_805930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805930 prefixEnd_805930 := by exact prefixLift 805930
  have htrace : WordTrace (prefixWord ++ tailWord_805930) baseStart_805930 baseEnd_805930 := by
    simpa [prefixWord, tailWord_805930, baseEnd_805930] using wordTrace_append hprefix tailTrace_805930
  have hstable : (prefixWord ++ tailWord_805930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805930).length < 2 ^ (prefixWord ++ tailWord_805930).sum := by decide
  have hdescent : baseEnd_805930 < baseStart_805930 := by decide
  rcases family_descends (prefixWord ++ tailWord_805930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805931 : List Nat := [1, 1, 1, 1, 2, 1, 13]
def baseStart_805931 : Nat := 118140960795 + 805931 * 2 ^ 59
def prefixEnd_805931 : Nat := 4983230072969 + 3 ^ 40 * 805931 * 2
def baseEnd_805931 : Nat := 40872096529263360489491

theorem tailTrace_805931 : CollatzResearch.WordTrace tailWord_805931 prefixEnd_805931 40872096529263360489491 := by
  unfold tailWord_805931
  simp only [CollatzResearch.WordTrace]
  refine ⟨29394718443257103901665647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19596478962171402601110431 29394718443257103901665647)
  ·
    refine ⟨44092077664885655852498471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29394718443257103901665647 44092077664885655852498471)
    ·
      refine ⟨66138116497328483778747707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44092077664885655852498471 66138116497328483778747707)
      ·
        refine ⟨99207174745992725668121561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66138116497328483778747707 99207174745992725668121561)
        ·
          refine ⟨74405381059494544251091171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99207174745992725668121561 74405381059494544251091171)
          ·
            refine ⟨111608071589241816376636757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74405381059494544251091171 111608071589241816376636757)
            ·
              refine ⟨40872096529263360489491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 111608071589241816376636757 40872096529263360489491)
              ·
                rfl

theorem cell20_805931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_805931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805931 prefixEnd_805931 := by exact prefixLift 805931
  have htrace : WordTrace (prefixWord ++ tailWord_805931) baseStart_805931 baseEnd_805931 := by
    simpa [prefixWord, tailWord_805931, baseEnd_805931] using wordTrace_append hprefix tailTrace_805931
  have hstable : (prefixWord ++ tailWord_805931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805931).length < 2 ^ (prefixWord ++ tailWord_805931).sum := by decide
  have hdescent : baseEnd_805931 < baseStart_805931 := by decide
  rcases family_descends (prefixWord ++ tailWord_805931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805934 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_805934 : Nat := 118140960795 + 805934 * 2 ^ 59
def prefixEnd_805934 : Nat := 4983230072969 + 3 ^ 40 * 805934 * 2
def baseEnd_805934 : Nat := 367850238045115567305407

theorem tailTrace_805934 : CollatzResearch.WordTrace tailWord_805934 prefixEnd_805934 367850238045115567305407 := by
  unfold tailWord_805934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674353482780779426753107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19596551908164156942683237 3674353482780779426753107)
  ·
    refine ⟨5511530224171169140129661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674353482780779426753107 5511530224171169140129661)
    ·
      refine ⟨2066823834064188427548623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5511530224171169140129661 2066823834064188427548623)
      ·
        refine ⟨3100235751096282641322935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066823834064188427548623 3100235751096282641322935)
        ·
          refine ⟨4650353626644423961984403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100235751096282641322935 4650353626644423961984403)
          ·
            refine ⟨6975530439966635942976605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650353626644423961984403 6975530439966635942976605)
            ·
              refine ⟨2615823914987488478616227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6975530439966635942976605 2615823914987488478616227)
              ·
                refine ⟨3923735872481232717924341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615823914987488478616227 3923735872481232717924341)
                ·
                  refine ⟨367850238045115567305407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3923735872481232717924341 367850238045115567305407)
                  ·
                    rfl

theorem cell20_805934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_805934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805934 prefixEnd_805934 := by exact prefixLift 805934
  have htrace : WordTrace (prefixWord ++ tailWord_805934) baseStart_805934 baseEnd_805934 := by
    simpa [prefixWord, tailWord_805934, baseEnd_805934] using wordTrace_append hprefix tailTrace_805934
  have hstable : (prefixWord ++ tailWord_805934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805934).length < 2 ^ (prefixWord ++ tailWord_805934).sum := by decide
  have hdescent : baseEnd_805934 < baseStart_805934 := by decide
  rcases family_descends (prefixWord ++ tailWord_805934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805965 : List Nat := [1, 6, 1, 1, 1, 3, 1, 6]
def baseStart_805965 : Nat := 118140960795 + 805965 * 2 ^ 59
def prefixEnd_805965 : Nat := 4983230072969 + 3 ^ 40 * 805965 * 2
def baseEnd_805965 : Nat := 122621462429939079090649

theorem tailTrace_805965 : CollatzResearch.WordTrace tailWord_805965 prefixEnd_805965 122621462429939079090649 := by
  unfold tailWord_805965
  simp only [CollatzResearch.WordTrace]
  refine ⟨29395958525133927708403349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19597305683422618472268899 29395958525133927708403349)
  ·
    refine ⟨1377935555865652861331407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29395958525133927708403349 1377935555865652861331407)
    ·
      refine ⟨2066903333798479291997111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377935555865652861331407 2066903333798479291997111)
      ·
        refine ⟨3100355000697718937995667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066903333798479291997111 3100355000697718937995667)
        ·
          refine ⟨4650532501046578406993501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100355000697718937995667 4650532501046578406993501)
          ·
            refine ⟨1743949687892466902622563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4650532501046578406993501 1743949687892466902622563)
            ·
              refine ⟨2615924531838700353933845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743949687892466902622563 2615924531838700353933845)
              ·
                refine ⟨122621462429939079090649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2615924531838700353933845 122621462429939079090649)
                ·
                  rfl

theorem cell20_805965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_805965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805965 prefixEnd_805965 := by exact prefixLift 805965
  have htrace : WordTrace (prefixWord ++ tailWord_805965) baseStart_805965 baseEnd_805965 := by
    simpa [prefixWord, tailWord_805965, baseEnd_805965] using wordTrace_append hprefix tailTrace_805965
  have hstable : (prefixWord ++ tailWord_805965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805965).length < 2 ^ (prefixWord ++ tailWord_805965).sum := by decide
  have hdescent : baseEnd_805965 < baseStart_805965 := by decide
  rcases family_descends (prefixWord ++ tailWord_805965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805982 : List Nat := [4, 4, 1, 1, 1, 1, 8]
def baseStart_805982 : Nat := 118140960795 + 805982 * 2 ^ 59
def prefixEnd_805982 : Nat := 4983230072969 + 3 ^ 40 * 805982 * 2
def baseEnd_805982 : Nat := 40874682950337859300579

theorem tailTrace_805982 : CollatzResearch.WordTrace tailWord_805982 prefixEnd_805982 40874682950337859300579 := by
  unfold tailWord_805982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674572320759042451471525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19597719044048226407848133 3674572320759042451471525)
  ·
    refine ⟨688982310142320459650911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3674572320759042451471525 688982310142320459650911)
    ·
      refine ⟨1033473465213480689476367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 688982310142320459650911 1033473465213480689476367)
      ·
        refine ⟨1550210197820221034214551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033473465213480689476367 1550210197820221034214551)
        ·
          refine ⟨2325315296730331551321827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550210197820221034214551 2325315296730331551321827)
          ·
            refine ⟨3487972945095497326982741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325315296730331551321827 3487972945095497326982741)
            ·
              refine ⟨40874682950337859300579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3487972945095497326982741 40874682950337859300579)
              ·
                rfl

theorem cell20_805982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 8].length) (baseStart_805982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805982 prefixEnd_805982 := by exact prefixLift 805982
  have htrace : WordTrace (prefixWord ++ tailWord_805982) baseStart_805982 baseEnd_805982 := by
    simpa [prefixWord, tailWord_805982, baseEnd_805982] using wordTrace_append hprefix tailTrace_805982
  have hstable : (prefixWord ++ tailWord_805982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805982).length < 2 ^ (prefixWord ++ tailWord_805982).sum := by decide
  have hdescent : baseEnd_805982 < baseStart_805982 := by decide
  rcases family_descends (prefixWord ++ tailWord_805982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805992 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 4]
def baseStart_805992 : Nat := 118140960795 + 805992 * 2 ^ 59
def prefixEnd_805992 : Nat := 4983230072969 + 3 ^ 40 * 805992 * 2
def baseEnd_805992 : Nat := 367876710825525143371837

theorem tailTrace_805992 : CollatzResearch.WordTrace tailWord_805992 prefixEnd_805992 367876710825525143371837 := by
  unfold tailWord_805992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14698471648018055659818115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19597962197357407546424153 14698471648018055659818115)
  ·
    refine ⟨22047707472027083489727173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14698471648018055659818115 22047707472027083489727173)
    ·
      refine ⟨4133945151005078154323845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22047707472027083489727173 4133945151005078154323845)
      ·
        refine ⟨775114715813452153935721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4133945151005078154323845 775114715813452153935721)
        ·
          refine ⟨581336036860089115451791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775114715813452153935721 581336036860089115451791)
          ·
            refine ⟨872004055290133673177687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581336036860089115451791 872004055290133673177687)
            ·
              refine ⟨1308006082935200509766531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872004055290133673177687 1308006082935200509766531)
              ·
                refine ⟨1962009124402800764649797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308006082935200509766531 1962009124402800764649797)
                ·
                  refine ⟨367876710825525143371837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962009124402800764649797 367876710825525143371837)
                  ·
                    rfl

theorem cell20_805992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_805992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805992 prefixEnd_805992 := by exact prefixLift 805992
  have htrace : WordTrace (prefixWord ++ tailWord_805992) baseStart_805992 baseEnd_805992 := by
    simpa [prefixWord, tailWord_805992, baseEnd_805992] using wordTrace_append hprefix tailTrace_805992
  have hstable : (prefixWord ++ tailWord_805992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805992).length < 2 ^ (prefixWord ++ tailWord_805992).sum := by decide
  have hdescent : baseEnd_805992 < baseStart_805992 := by decide
  rcases family_descends (prefixWord ++ tailWord_805992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805993 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_805993 : Nat := 118140960795 + 805993 * 2 ^ 59
def prefixEnd_805993 : Nat := 4983230072969 + 3 ^ 40 * 805993 * 2
def baseEnd_805993 : Nat := 367877167252773584338499

theorem tailTrace_805993 : CollatzResearch.WordTrace tailWord_805993 prefixEnd_805993 367877167252773584338499 := by
  unfold tailWord_805993
  simp only [CollatzResearch.WordTrace]
  refine ⟨29396979769032488490422633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19597986512688325660281755 29396979769032488490422633)
  ·
    refine ⟨22047734826774366367816975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29396979769032488490422633 22047734826774366367816975)
    ·
      refine ⟨33071602240161549551725463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22047734826774366367816975 33071602240161549551725463)
      ·
        refine ⟨49607403360242324327588195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33071602240161549551725463 49607403360242324327588195)
        ·
          refine ⟨74411105040363486491382293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49607403360242324327588195 74411105040363486491382293)
          ·
            refine ⟨3488020548767038429283545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74411105040363486491382293 3488020548767038429283545)
            ·
              refine ⟨2616015411575278821962659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3488020548767038429283545 2616015411575278821962659)
              ·
                refine ⟨3924023117362918232943989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616015411575278821962659 3924023117362918232943989)
                ·
                  refine ⟨367877167252773584338499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3924023117362918232943989 367877167252773584338499)
                  ·
                    rfl

theorem cell20_805993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_805993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_805993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_805993 prefixEnd_805993 := by exact prefixLift 805993
  have htrace : WordTrace (prefixWord ++ tailWord_805993) baseStart_805993 baseEnd_805993 := by
    simpa [prefixWord, tailWord_805993, baseEnd_805993] using wordTrace_append hprefix tailTrace_805993
  have hstable : (prefixWord ++ tailWord_805993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805993).length < 2 ^ (prefixWord ++ tailWord_805993).sum := by decide
  have hdescent : baseEnd_805993 < baseStart_805993 := by decide
  rcases family_descends (prefixWord ++ tailWord_805993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806047 : List Nat := [1, 1, 2, 6, 3, 1, 2, 2, 2]
def baseStart_806047 : Nat := 118140960795 + 806047 * 2 ^ 59
def prefixEnd_806047 : Nat := 4983230072969 + 3 ^ 40 * 806047 * 2
def baseEnd_806047 : Nat := 367901814324189396538279

theorem tailTrace_806047 : CollatzResearch.WordTrace tailWord_806047 prefixEnd_806047 367901814324189396538279 := by
  unfold tailWord_806047
  simp only [CollatzResearch.WordTrace]
  refine ⟨29398949310836855712888395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19599299540557903808592263 29398949310836855712888395)
  ·
    refine ⟨44098423966255283569332593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29398949310836855712888395 44098423966255283569332593)
    ·
      refine ⟨33073817974691462676999445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44098423966255283569332593 33073817974691462676999445)
      ·
        refine ⟨1550335217563662312984349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33073817974691462676999445 1550335217563662312984349)
        ·
          refine ⟨581375706586373367369131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1550335217563662312984349 581375706586373367369131)
          ·
            refine ⟨872063559879560051053697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581375706586373367369131 872063559879560051053697)
            ·
              refine ⟨654047669909670038290273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872063559879560051053697 654047669909670038290273)
              ·
                refine ⟨490535752432252528717705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654047669909670038290273 490535752432252528717705)
                ·
                  refine ⟨367901814324189396538279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490535752432252528717705 367901814324189396538279)
                  ·
                    rfl

theorem cell20_806047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 2].length) (baseStart_806047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806047 prefixEnd_806047 := by exact prefixLift 806047
  have htrace : WordTrace (prefixWord ++ tailWord_806047) baseStart_806047 baseEnd_806047 := by
    simpa [prefixWord, tailWord_806047, baseEnd_806047] using wordTrace_append hprefix tailTrace_806047
  have hstable : (prefixWord ++ tailWord_806047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806047).length < 2 ^ (prefixWord ++ tailWord_806047).sum := by decide
  have hdescent : baseEnd_806047 < baseStart_806047 := by decide
  rcases family_descends (prefixWord ++ tailWord_806047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806048 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_806048 : Nat := 118140960795 + 806048 * 2 ^ 59
def prefixEnd_806048 : Nat := 4983230072969 + 3 ^ 40 * 806048 * 2
def baseEnd_806048 : Nat := 367902270751437837504941

theorem tailTrace_806048 : CollatzResearch.WordTrace tailWord_806048 prefixEnd_806048 367902270751437837504941 := by
  unfold tailWord_806048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14699492891916616441837399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19599323855888821922449865 14699492891916616441837399)
  ·
    refine ⟨22049239337874924662756099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14699492891916616441837399 22049239337874924662756099)
    ·
      refine ⟨33073859006812386994134149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22049239337874924662756099 33073859006812386994134149)
      ·
        refine ⟨6201348563777322561400153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33073859006812386994134149 6201348563777322561400153)
        ·
          refine ⟨4651011422832991921050115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6201348563777322561400153 4651011422832991921050115)
          ·
            refine ⟨6976517134249487881575173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4651011422832991921050115 6976517134249487881575173)
            ·
              refine ⟨1308096962671778977795345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6976517134249487881575173 1308096962671778977795345)
              ·
                refine ⟨981072722003834233346509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308096962671778977795345 981072722003834233346509)
                ·
                  refine ⟨367902270751437837504941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981072722003834233346509 367902270751437837504941)
                  ·
                    rfl

theorem cell20_806048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_806048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806048 prefixEnd_806048 := by exact prefixLift 806048
  have htrace : WordTrace (prefixWord ++ tailWord_806048) baseStart_806048 baseEnd_806048 := by
    simpa [prefixWord, tailWord_806048, baseEnd_806048] using wordTrace_append hprefix tailTrace_806048
  have hstable : (prefixWord ++ tailWord_806048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806048).length < 2 ^ (prefixWord ++ tailWord_806048).sum := by decide
  have hdescent : baseEnd_806048 < baseStart_806048 := by decide
  rcases family_descends (prefixWord ++ tailWord_806048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806058 : List Nat := [3, 1, 5, 1, 1, 3, 1, 5]
def baseStart_806058 : Nat := 118140960795 + 806058 * 2 ^ 59
def prefixEnd_806058 : Nat := 4983230072969 + 3 ^ 40 * 806058 * 2
def baseEnd_806058 : Nat := 122635611674640749057189

theorem tailTrace_806058 : CollatzResearch.WordTrace tailWord_806058 prefixEnd_806058 122635611674640749057189 := by
  unfold tailWord_806058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349837628449251147884707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19599567009198003061025885 7349837628449251147884707)
  ·
    refine ⟨11024756442673876721827061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7349837628449251147884707 11024756442673876721827061)
    ·
      refine ⟨1033570916500675942671287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11024756442673876721827061 1033570916500675942671287)
      ·
        refine ⟨1550356374751013914006931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033570916500675942671287 1550356374751013914006931)
        ·
          refine ⟨2325534562126520871010397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550356374751013914006931 2325534562126520871010397)
          ·
            refine ⟨872075460797445326628899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2325534562126520871010397 872075460797445326628899)
            ·
              refine ⟨1308113191196167989943349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872075460797445326628899 1308113191196167989943349)
              ·
                refine ⟨122635611674640749057189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1308113191196167989943349 122635611674640749057189)
                ·
                  rfl

theorem cell20_806058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_806058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806058 prefixEnd_806058 := by exact prefixLift 806058
  have htrace : WordTrace (prefixWord ++ tailWord_806058) baseStart_806058 baseEnd_806058 := by
    simpa [prefixWord, tailWord_806058, baseEnd_806058] using wordTrace_append hprefix tailTrace_806058
  have hstable : (prefixWord ++ tailWord_806058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806058).length < 2 ^ (prefixWord ++ tailWord_806058).sum := by decide
  have hdescent : baseEnd_806058 < baseStart_806058 := by decide
  rcases family_descends (prefixWord ++ tailWord_806058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806145 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_806145 : Nat := 118140960795 + 806145 * 2 ^ 59
def prefixEnd_806145 : Nat := 4983230072969 + 3 ^ 40 * 806145 * 2
def baseEnd_806145 : Nat := 367946544194536611271211

theorem tailTrace_806145 : CollatzResearch.WordTrace tailWord_806145 prefixEnd_806145 367946544194536611271211 := by
  unfold tailWord_806145
  simp only [CollatzResearch.WordTrace]
  refine ⟨29402523664481818449955889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19601682442987878966637259 29402523664481818449955889)
  ·
    refine ⟨22051892748361363837466917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29402523664481818449955889 22051892748361363837466917)
    ·
      refine ⟨4134729890317755719525047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22051892748361363837466917 4134729890317755719525047)
      ·
        refine ⟨6202094835476633579287571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4134729890317755719525047 6202094835476633579287571)
        ·
          refine ⟨9303142253214950368931357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202094835476633579287571 9303142253214950368931357)
          ·
            refine ⟨3488678344955606388349259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9303142253214950368931357 3488678344955606388349259)
            ·
              refine ⟨5233017517433409582523889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488678344955606388349259 5233017517433409582523889)
              ·
                refine ⟨3924763138075057186892917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233017517433409582523889 3924763138075057186892917)
                ·
                  refine ⟨367946544194536611271211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3924763138075057186892917 367946544194536611271211)
                  ·
                    rfl

theorem cell20_806145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_806145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806145 prefixEnd_806145 := by exact prefixLift 806145
  have htrace : WordTrace (prefixWord ++ tailWord_806145) baseStart_806145 baseEnd_806145 := by
    simpa [prefixWord, tailWord_806145, baseEnd_806145] using wordTrace_append hprefix tailTrace_806145
  have hstable : (prefixWord ++ tailWord_806145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806145).length < 2 ^ (prefixWord ++ tailWord_806145).sum := by decide
  have hdescent : baseEnd_806145 < baseStart_806145 := by decide
  rcases family_descends (prefixWord ++ tailWord_806145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806179 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 3]
def baseStart_806179 : Nat := 118140960795 + 806179 * 2 ^ 59
def prefixEnd_806179 : Nat := 4983230072969 + 3 ^ 40 * 806179 * 2
def baseEnd_806179 : Nat := 367962062720983604137739

theorem tailTrace_806179 : CollatzResearch.WordTrace tailWord_806179 prefixEnd_806179 367962062720983604137739 := by
  unfold tailWord_806179
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403763746358642256693591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19602509164239094837795727 29403763746358642256693591)
  ·
    refine ⟨44105645619537963385040387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29403763746358642256693591 44105645619537963385040387)
    ·
      refine ⟨66158468429306945077560581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44105645619537963385040387 66158468429306945077560581)
      ·
        refine ⟨12404712830495052202042609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66158468429306945077560581 12404712830495052202042609)
        ·
          refine ⟨9303534622871289151531957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12404712830495052202042609 9303534622871289151531957)
          ·
            refine ⟨872206370894183357956121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9303534622871289151531957 872206370894183357956121)
            ·
              refine ⟨654154778170637518467091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872206370894183357956121 654154778170637518467091)
              ·
                refine ⟨981232167255956277700637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654154778170637518467091 981232167255956277700637)
                ·
                  refine ⟨367962062720983604137739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981232167255956277700637 367962062720983604137739)
                  ·
                    rfl

theorem cell20_806179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 3].length) (baseStart_806179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806179 prefixEnd_806179 := by exact prefixLift 806179
  have htrace : WordTrace (prefixWord ++ tailWord_806179) baseStart_806179 baseEnd_806179 := by
    simpa [prefixWord, tailWord_806179, baseEnd_806179] using wordTrace_append hprefix tailTrace_806179
  have hstable : (prefixWord ++ tailWord_806179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806179).length < 2 ^ (prefixWord ++ tailWord_806179).sum := by decide
  have hdescent : baseEnd_806179 < baseStart_806179 := by decide
  rcases family_descends (prefixWord ++ tailWord_806179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806276 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_806276 : Nat := 118140960795 + 806276 * 2 ^ 59
def prefixEnd_806276 : Nat := 4983230072969 + 3 ^ 40 * 806276 * 2
def baseEnd_806276 : Nat := 368006336164082377904009

theorem tailTrace_806276 : CollatzResearch.WordTrace tailWord_806276 prefixEnd_806276 368006336164082377904009 := by
  unfold tailWord_806276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14703650813503613911487341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19604867751338151881983121 14703650813503613911487341)
  ·
    refine ⟨5513869055063855216807753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14703650813503613911487341 5513869055063855216807753)
    ·
      refine ⟨4135401791297891412605815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5513869055063855216807753 4135401791297891412605815)
      ·
        refine ⟨6203102686946837118908723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135401791297891412605815 6203102686946837118908723)
        ·
          refine ⟨9304654030420255678363085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203102686946837118908723 9304654030420255678363085)
          ·
            refine ⟨3489245261407595879386157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9304654030420255678363085 3489245261407595879386157)
            ·
              refine ⟨1308466973027848454769809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3489245261407595879386157 1308466973027848454769809)
              ·
                refine ⟨981350229770886341077357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308466973027848454769809 981350229770886341077357)
                ·
                  refine ⟨368006336164082377904009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981350229770886341077357 368006336164082377904009)
                  ·
                    rfl

theorem cell20_806276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_806276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806276 prefixEnd_806276 := by exact prefixLift 806276
  have htrace : WordTrace (prefixWord ++ tailWord_806276) baseStart_806276 baseEnd_806276 := by
    simpa [prefixWord, tailWord_806276, baseEnd_806276] using wordTrace_append hprefix tailTrace_806276
  have hstable : (prefixWord ++ tailWord_806276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806276).length < 2 ^ (prefixWord ++ tailWord_806276).sum := by decide
  have hdescent : baseEnd_806276 < baseStart_806276 := by decide
  rcases family_descends (prefixWord ++ tailWord_806276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806283 : List Nat := [1, 1, 1, 1, 4, 3, 1, 6, 2]
def baseStart_806283 : Nat := 118140960795 + 806283 * 2 ^ 59
def prefixEnd_806283 : Nat := 4983230072969 + 3 ^ 40 * 806283 * 2
def baseEnd_806283 : Nat := 368009531154821464670647

theorem tailTrace_806283 : CollatzResearch.WordTrace tailWord_806283 prefixEnd_806283 368009531154821464670647 := by
  unfold tailWord_806283
  simp only [CollatzResearch.WordTrace]
  refine ⟨29407556937981868018479503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19605037958654578678986335 29407556937981868018479503)
  ·
    refine ⟨44111335406972802027719255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29407556937981868018479503 44111335406972802027719255)
    ·
      refine ⟨66167003110459203041578883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44111335406972802027719255 66167003110459203041578883)
      ·
        refine ⟨99250504665688804562368325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66167003110459203041578883 99250504665688804562368325)
        ·
          refine ⟨18609469624816650855444061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99250504665688804562368325 18609469624816650855444061)
          ·
            refine ⟨6978551109306244070791523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18609469624816650855444061 6978551109306244070791523)
            ·
              refine ⟨10467826663959366106187285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6978551109306244070791523 10467826663959366106187285)
              ·
                refine ⟨490679374873095286227529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10467826663959366106187285 490679374873095286227529)
                ·
                  refine ⟨368009531154821464670647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490679374873095286227529 368009531154821464670647)
                  ·
                    rfl

theorem cell20_806283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 2].length) (baseStart_806283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806283 prefixEnd_806283 := by exact prefixLift 806283
  have htrace : WordTrace (prefixWord ++ tailWord_806283) baseStart_806283 baseEnd_806283 := by
    simpa [prefixWord, tailWord_806283, baseEnd_806283] using wordTrace_append hprefix tailTrace_806283
  have hstable : (prefixWord ++ tailWord_806283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806283).length < 2 ^ (prefixWord ++ tailWord_806283).sum := by decide
  have hdescent : baseEnd_806283 < baseStart_806283 := by decide
  rcases family_descends (prefixWord ++ tailWord_806283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806304 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_806304 : Nat := 118140960795 + 806304 * 2 ^ 59
def prefixEnd_806304 : Nat := 4983230072969 + 3 ^ 40 * 806304 * 2
def baseEnd_806304 : Nat := 368019116127038724970561

theorem tailTrace_806304 : CollatzResearch.WordTrace tailWord_806304 prefixEnd_806304 368019116127038724970561 := by
  unfold tailWord_806304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14704161435452894302496983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19605548580603859069995977 14704161435452894302496983)
  ·
    refine ⟨22056242153179341453745475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14704161435452894302496983 22056242153179341453745475)
    ·
      refine ⟨33084363229769012180618213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22056242153179341453745475 33084363229769012180618213)
      ·
        refine ⟨6203318105581689783865915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33084363229769012180618213 6203318105581689783865915)
        ·
          refine ⟨9304977158372534675798873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203318105581689783865915 9304977158372534675798873)
          ·
            refine ⟨6978732868779401006849155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9304977158372534675798873 6978732868779401006849155)
            ·
              refine ⟨10468099303169101510273733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6978732868779401006849155 10468099303169101510273733)
              ·
                refine ⟨1962768619344206533176325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10468099303169101510273733 1962768619344206533176325)
                ·
                  refine ⟨368019116127038724970561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1962768619344206533176325 368019116127038724970561)
                  ·
                    rfl

theorem cell20_806304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_806304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806304 prefixEnd_806304 := by exact prefixLift 806304
  have htrace : WordTrace (prefixWord ++ tailWord_806304) baseStart_806304 baseEnd_806304 := by
    simpa [prefixWord, tailWord_806304, baseEnd_806304] using wordTrace_append hprefix tailTrace_806304
  have hstable : (prefixWord ++ tailWord_806304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806304).length < 2 ^ (prefixWord ++ tailWord_806304).sum := by decide
  have hdescent : baseEnd_806304 < baseStart_806304 := by decide
  rcases family_descends (prefixWord ++ tailWord_806304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806317 : List Nat := [1, 5, 2, 2, 1, 1, 3, 3, 2]
def baseStart_806317 : Nat := 118140960795 + 806317 * 2 ^ 59
def prefixEnd_806317 : Nat := 4983230072969 + 3 ^ 40 * 806317 * 2
def baseEnd_806317 : Nat := 368025049681268457537175

theorem tailTrace_806317 : CollatzResearch.WordTrace tailWord_806317 prefixEnd_806317 368025049681268457537175 := by
  unfold tailWord_806317
  simp only [CollatzResearch.WordTrace]
  refine ⟨29408797019858691825217205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19605864679905794550144803 29408797019858691825217205)
  ·
    refine ⟨2757074720611752358614113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29408797019858691825217205 2757074720611752358614113)
    ·
      refine ⟨2067806040458814268960585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2757074720611752358614113 2067806040458814268960585)
      ·
        refine ⟨1550854530344110701720439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2067806040458814268960585 1550854530344110701720439)
        ·
          refine ⟨2326281795516166052580659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550854530344110701720439 2326281795516166052580659)
          ·
            refine ⟨3489422693274249078870989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326281795516166052580659 3489422693274249078870989)
            ·
              refine ⟨1308533509977843404576621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3489422693274249078870989 1308533509977843404576621)
              ·
                refine ⟨490700066241691276716233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1308533509977843404576621 490700066241691276716233)
                ·
                  refine ⟨368025049681268457537175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490700066241691276716233 368025049681268457537175)
                  ·
                    rfl

theorem cell20_806317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_806317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806317 prefixEnd_806317 := by exact prefixLift 806317
  have htrace : WordTrace (prefixWord ++ tailWord_806317) baseStart_806317 baseEnd_806317 := by
    simpa [prefixWord, tailWord_806317, baseEnd_806317] using wordTrace_append hprefix tailTrace_806317
  have hstable : (prefixWord ++ tailWord_806317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806317).length < 2 ^ (prefixWord ++ tailWord_806317).sum := by decide
  have hdescent : baseEnd_806317 < baseStart_806317 := by decide
  rcases family_descends (prefixWord ++ tailWord_806317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806390 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_806390 : Nat := 118140960795 + 806390 * 2 ^ 59
def prefixEnd_806390 : Nat := 4983230072969 + 3 ^ 40 * 806390 * 2
def baseEnd_806390 : Nat := 368058368870404648103543

theorem tailTrace_806390 : CollatzResearch.WordTrace tailWord_806390 prefixEnd_806390 368058368870404648103543 := by
  unfold tailWord_806390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838216221787139080789039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19607639699062816861749749 1838216221787139080789039)
  ·
    refine ⟨2757324332680708621183559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1838216221787139080789039 2757324332680708621183559)
    ·
      refine ⟨4135986499021062931775339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757324332680708621183559 4135986499021062931775339)
      ·
        refine ⟨6203979748531594397663009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135986499021062931775339 6203979748531594397663009)
        ·
          refine ⟨4652984811398695798247257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6203979748531594397663009 4652984811398695798247257)
          ·
            refine ⟨3489738608549021848685443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4652984811398695798247257 3489738608549021848685443)
            ·
              refine ⟨5234607912823532773028165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489738608549021848685443 5234607912823532773028165)
              ·
                refine ⟨981488983654412394942781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5234607912823532773028165 981488983654412394942781)
                ·
                  refine ⟨368058368870404648103543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981488983654412394942781 368058368870404648103543)
                  ·
                    rfl

theorem cell20_806390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_806390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806390 prefixEnd_806390 := by exact prefixLift 806390
  have htrace : WordTrace (prefixWord ++ tailWord_806390) baseStart_806390 baseEnd_806390 := by
    simpa [prefixWord, tailWord_806390, baseEnd_806390] using wordTrace_append hprefix tailTrace_806390
  have hstable : (prefixWord ++ tailWord_806390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806390).length < 2 ^ (prefixWord ++ tailWord_806390).sum := by decide
  have hdescent : baseEnd_806390 < baseStart_806390 := by decide
  rcases family_descends (prefixWord ++ tailWord_806390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806456 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_806456 : Nat := 118140960795 + 806456 * 2 ^ 59
def prefixEnd_806456 : Nat := 4983230072969 + 3 ^ 40 * 806456 * 2
def baseEnd_806456 : Nat := 368088493068801751903273

theorem tailTrace_806456 : CollatzResearch.WordTrace tailWord_806456 prefixEnd_806456 368088493068801751903273 := by
  unfold tailWord_806456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14706933383177559282263611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19609244510903412376351481 14706933383177559282263611)
  ·
    refine ⟨22060400074766338923395417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14706933383177559282263611 22060400074766338923395417)
    ·
      refine ⟨16545300056074754192546563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22060400074766338923395417 16545300056074754192546563)
      ·
        refine ⟨24817950084112131288819845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16545300056074754192546563 24817950084112131288819845)
        ·
          refine ⟨4653365640771024616653721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24817950084112131288819845 4653365640771024616653721)
          ·
            refine ⟨3490024230578268462490291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4653365640771024616653721 3490024230578268462490291)
            ·
              refine ⟨5235036345867402693735437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490024230578268462490291 5235036345867402693735437)
              ·
                refine ⟨1963138629700276010150789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5235036345867402693735437 1963138629700276010150789)
                ·
                  refine ⟨368088493068801751903273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963138629700276010150789 368088493068801751903273)
                  ·
                    rfl

theorem cell20_806456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_806456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806456 prefixEnd_806456 := by exact prefixLift 806456
  have htrace : WordTrace (prefixWord ++ tailWord_806456) baseStart_806456 baseEnd_806456 := by
    simpa [prefixWord, tailWord_806456, baseEnd_806456] using wordTrace_append hprefix tailTrace_806456
  have hstable : (prefixWord ++ tailWord_806456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806456).length < 2 ^ (prefixWord ++ tailWord_806456).sum := by decide
  have hdescent : baseEnd_806456 < baseStart_806456 := by decide
  rcases family_descends (prefixWord ++ tailWord_806456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806501 : List Nat := [1, 3, 1, 3, 3, 1, 8]
def baseStart_806501 : Nat := 118140960795 + 806501 * 2 ^ 59
def prefixEnd_806501 : Nat := 4983230072969 + 3 ^ 40 * 806501 * 2
def baseEnd_806501 : Nat := 40901003588331288378121

theorem tailTrace_806501 : CollatzResearch.WordTrace tailWord_806501 prefixEnd_806501 40901003588331288378121 := by
  unfold tailWord_806501
  simp only [CollatzResearch.WordTrace]
  refine ⟨29415508051192091249915357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19610338700794727499943571 29415508051192091249915357)
  ·
    refine ⟨11030815519197034218718259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29415508051192091249915357 11030815519197034218718259)
    ·
      refine ⟨16546223278795551328077389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11030815519197034218718259 16546223278795551328077389)
      ·
        refine ⟨6204833729548331748029021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16546223278795551328077389 6204833729548331748029021)
        ·
          refine ⟨2326812648580624405510883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6204833729548331748029021 2326812648580624405510883)
          ·
            refine ⟨3490218972870936608266325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326812648580624405510883 3490218972870936608266325)
            ·
              refine ⟨40901003588331288378121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3490218972870936608266325 40901003588331288378121)
              ·
                rfl

theorem cell20_806501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_806501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806501 prefixEnd_806501 := by exact prefixLift 806501
  have htrace : WordTrace (prefixWord ++ tailWord_806501) baseStart_806501 baseEnd_806501 := by
    simpa [prefixWord, tailWord_806501, baseEnd_806501] using wordTrace_append hprefix tailTrace_806501
  have hstable : (prefixWord ++ tailWord_806501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806501).length < 2 ^ (prefixWord ++ tailWord_806501).sum := by decide
  have hdescent : baseEnd_806501 < baseStart_806501 := by decide
  rcases family_descends (prefixWord ++ tailWord_806501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806518 : List Nat := [5, 1, 1, 2, 2, 1, 1, 7]
def baseStart_806518 : Nat := 118140960795 + 806518 * 2 ^ 59
def prefixEnd_806518 : Nat := 4983230072969 + 3 ^ 40 * 806518 * 2
def baseEnd_806518 : Nat := 122705597186068363945451

theorem tailTrace_806518 : CollatzResearch.WordTrace tailWord_806518 prefixEnd_806518 122705597186068363945451 := by
  unfold tailWord_806518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838508005758156447080263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19610752061420335435522805 1838508005758156447080263)
  ·
    refine ⟨2757762008637234670620395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1838508005758156447080263 2757762008637234670620395)
    ·
      refine ⟨4136643012955852005930593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757762008637234670620395 4136643012955852005930593)
      ·
        refine ⟨3102482259716889004447945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136643012955852005930593 3102482259716889004447945)
        ·
          refine ⟨2326861694787666753335959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102482259716889004447945 2326861694787666753335959)
          ·
            refine ⟨3490292542181500130003939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326861694787666753335959 3490292542181500130003939)
            ·
              refine ⟨5235438813272250195005909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490292542181500130003939 5235438813272250195005909)
              ·
                refine ⟨122705597186068363945451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5235438813272250195005909 122705597186068363945451)
                ·
                  rfl

theorem cell20_806518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_806518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806518 prefixEnd_806518 := by exact prefixLift 806518
  have htrace : WordTrace (prefixWord ++ tailWord_806518) baseStart_806518 baseEnd_806518 := by
    simpa [prefixWord, tailWord_806518, baseEnd_806518] using wordTrace_append hprefix tailTrace_806518
  have hstable : (prefixWord ++ tailWord_806518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806518).length < 2 ^ (prefixWord ++ tailWord_806518).sum := by decide
  have hdescent : baseEnd_806518 < baseStart_806518 := by decide
  rcases family_descends (prefixWord ++ tailWord_806518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806553 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_806553 : Nat := 118140960795 + 806553 * 2 ^ 59
def prefixEnd_806553 : Nat := 4983230072969 + 3 ^ 40 * 806553 * 2
def baseEnd_806553 : Nat := 368132766511900525669543

theorem tailTrace_806553 : CollatzResearch.WordTrace tailWord_806553 prefixEnd_806553 368132766511900525669543 := by
  unfold tailWord_806553
  simp only [CollatzResearch.WordTrace]
  refine ⟨29417404647003704130808313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19611603098002469420538875 29417404647003704130808313)
  ·
    refine ⟨22063053485252778098106235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29417404647003704130808313 22063053485252778098106235)
    ·
      refine ⟨33094580227879167147159353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22063053485252778098106235 33094580227879167147159353)
      ·
        refine ⟨24820935170909375360369515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33094580227879167147159353 24820935170909375360369515)
        ·
          refine ⟨37231402756364063040554273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24820935170909375360369515 37231402756364063040554273)
          ·
            refine ⟨27923552067273047280415705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37231402756364063040554273 27923552067273047280415705)
            ·
              refine ⟨20942664050454785460311779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27923552067273047280415705 20942664050454785460311779)
              ·
                refine ⟨31413996075682178190467669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20942664050454785460311779 31413996075682178190467669)
                ·
                  refine ⟨368132766511900525669543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31413996075682178190467669 368132766511900525669543)
                  ·
                    rfl

theorem cell20_806553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_806553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806553 prefixEnd_806553 := by exact prefixLift 806553
  have htrace : WordTrace (prefixWord ++ tailWord_806553) baseStart_806553 baseEnd_806553 := by
    simpa [prefixWord, tailWord_806553, baseEnd_806553] using wordTrace_append hprefix tailTrace_806553
  have hstable : (prefixWord ++ tailWord_806553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806553).length < 2 ^ (prefixWord ++ tailWord_806553).sum := by decide
  have hdescent : baseEnd_806553 < baseStart_806553 := by decide
  rcases family_descends (prefixWord ++ tailWord_806553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806556 : List Nat := [2, 2, 3, 2, 4, 7]
def baseStart_806556 : Nat := 118140960795 + 806556 * 2 ^ 59
def prefixEnd_806556 : Nat := 4983230072969 + 3 ^ 40 * 806556 * 2
def baseEnd_806556 : Nat := 13634597621986883280353

theorem tailTrace_806556 : CollatzResearch.WordTrace tailWord_806556 prefixEnd_806556 13634597621986883280353 := by
  unfold tailWord_806556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708757032996417821583761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19611676043995223762111681 14708757032996417821583761)
  ·
    refine ⟨11031567774747313366187821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14708757032996417821583761 11031567774747313366187821)
    ·
      refine ⟨4136837915530242512320433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11031567774747313366187821 4136837915530242512320433)
      ·
        refine ⟨3102628436647681884240325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136837915530242512320433 3102628436647681884240325)
        ·
          refine ⟨581742831871440353295061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3102628436647681884240325 581742831871440353295061)
          ·
            refine ⟨13634597621986883280353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 581742831871440353295061 13634597621986883280353)
            ·
              rfl

theorem cell20_806556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 7].length) (baseStart_806556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806556 prefixEnd_806556 := by exact prefixLift 806556
  have htrace : WordTrace (prefixWord ++ tailWord_806556) baseStart_806556 baseEnd_806556 := by
    simpa [prefixWord, tailWord_806556, baseEnd_806556] using wordTrace_append hprefix tailTrace_806556
  have hstable : (prefixWord ++ tailWord_806556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806556).length < 2 ^ (prefixWord ++ tailWord_806556).sum := by decide
  have hdescent : baseEnd_806556 < baseStart_806556 := by decide
  rcases family_descends (prefixWord ++ tailWord_806556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806559 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 3]
def baseStart_806559 : Nat := 118140960795 + 806559 * 2 ^ 59
def prefixEnd_806559 : Nat := 4983230072969 + 3 ^ 40 * 806559 * 2
def baseEnd_806559 : Nat := 368135505075391171469519

theorem tailTrace_806559 : CollatzResearch.WordTrace tailWord_806559 prefixEnd_806559 368135505075391171469519 := by
  unfold tailWord_806559
  simp only [CollatzResearch.WordTrace]
  refine ⟨29417623484981967155526731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19611748989987978103684487 29417623484981967155526731)
  ·
    refine ⟨44126435227472950733290097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29417623484981967155526731 44126435227472950733290097)
    ·
      refine ⟨33094826420604713049967573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44126435227472950733290097 33094826420604713049967573)
      ·
        refine ⟨775659994232922962108615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33094826420604713049967573 775659994232922962108615)
        ·
          refine ⟨1163489991349384443162923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775659994232922962108615 1163489991349384443162923)
          ·
            refine ⟨1745234987024076664744385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163489991349384443162923 1745234987024076664744385)
            ·
              refine ⟨1308926240268057498558289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745234987024076664744385 1308926240268057498558289)
              ·
                refine ⟨981694680201043123918717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308926240268057498558289 981694680201043123918717)
                ·
                  refine ⟨368135505075391171469519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981694680201043123918717 368135505075391171469519)
                  ·
                    rfl

theorem cell20_806559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_806559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806559 prefixEnd_806559 := by exact prefixLift 806559
  have htrace : WordTrace (prefixWord ++ tailWord_806559) baseStart_806559 baseEnd_806559 := by
    simpa [prefixWord, tailWord_806559, baseEnd_806559] using wordTrace_append hprefix tailTrace_806559
  have hstable : (prefixWord ++ tailWord_806559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806559).length < 2 ^ (prefixWord ++ tailWord_806559).sum := by decide
  have hdescent : baseEnd_806559 < baseStart_806559 := by decide
  rcases family_descends (prefixWord ++ tailWord_806559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806563 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 3]
def baseStart_806563 : Nat := 118140960795 + 806563 * 2 ^ 59
def prefixEnd_806563 : Nat := 4983230072969 + 3 ^ 40 * 806563 * 2
def baseEnd_806563 : Nat := 368137330784384935336169

theorem tailTrace_806563 : CollatzResearch.WordTrace tailWord_806563 prefixEnd_806563 368137330784384935336169 := by
  unfold tailWord_806563
  simp only [CollatzResearch.WordTrace]
  refine ⟨29417769376967475838672343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19611846251311650559114895 29417769376967475838672343)
  ·
    refine ⟨44126654065451213758008515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29417769376967475838672343 44126654065451213758008515)
    ·
      refine ⟨66189981098176820637012773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44126654065451213758008515 66189981098176820637012773)
      ·
        refine ⟨12410621455908153869439895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66189981098176820637012773 12410621455908153869439895)
        ·
          refine ⟨18615932183862230804159843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12410621455908153869439895 18615932183862230804159843)
          ·
            refine ⟨27923898275793346206239765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18615932183862230804159843 27923898275793346206239765)
            ·
              refine ⟨1308932731677813103417489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27923898275793346206239765 1308932731677813103417489)
              ·
                refine ⟨981699548758359827563117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308932731677813103417489 981699548758359827563117)
                ·
                  refine ⟨368137330784384935336169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981699548758359827563117 368137330784384935336169)
                  ·
                    rfl

theorem cell20_806563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_806563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806563 prefixEnd_806563 := by exact prefixLift 806563
  have htrace : WordTrace (prefixWord ++ tailWord_806563) baseStart_806563 baseEnd_806563 := by
    simpa [prefixWord, tailWord_806563, baseEnd_806563] using wordTrace_append hprefix tailTrace_806563
  have hstable : (prefixWord ++ tailWord_806563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806563).length < 2 ^ (prefixWord ++ tailWord_806563).sum := by decide
  have hdescent : baseEnd_806563 < baseStart_806563 := by decide
  rcases family_descends (prefixWord ++ tailWord_806563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806618 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_806618 : Nat := 118140960795 + 806618 * 2 ^ 59
def prefixEnd_806618 : Nat := 4983230072969 + 3 ^ 40 * 806618 * 2
def baseEnd_806618 : Nat := 368162434283049188502611

theorem tailTrace_806618 : CollatzResearch.WordTrace tailWord_806618 prefixEnd_806618 368162434283049188502611 := by
  unfold tailWord_806618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354943847942055057981127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19613183594512146821283005 7354943847942055057981127)
  ·
    refine ⟨11032415771913082586971691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7354943847942055057981127 11032415771913082586971691)
    ·
      refine ⟨16548623657869623880457537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11032415771913082586971691 16548623657869623880457537)
      ·
        refine ⟨12411467743402217910343153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16548623657869623880457537 12411467743402217910343153)
        ·
          refine ⟨9308600807551663432757365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12411467743402217910343153 9308600807551663432757365)
          ·
            refine ⟨872681325707968446821003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9308600807551663432757365 872681325707968446821003)
            ·
              refine ⟨1309021988561952670231505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872681325707968446821003 1309021988561952670231505)
              ·
                refine ⟨981766491421464502673629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309021988561952670231505 981766491421464502673629)
                ·
                  refine ⟨368162434283049188502611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981766491421464502673629 368162434283049188502611)
                  ·
                    rfl

theorem cell20_806618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_806618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806618 prefixEnd_806618 := by exact prefixLift 806618
  have htrace : WordTrace (prefixWord ++ tailWord_806618) baseStart_806618 baseEnd_806618 := by
    simpa [prefixWord, tailWord_806618, baseEnd_806618] using wordTrace_append hprefix tailTrace_806618
  have hstable : (prefixWord ++ tailWord_806618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806618).length < 2 ^ (prefixWord ++ tailWord_806618).sum := by decide
  have hdescent : baseEnd_806618 < baseStart_806618 := by decide
  rcases family_descends (prefixWord ++ tailWord_806618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806625 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 4]
def baseStart_806625 : Nat := 118140960795 + 806625 * 2 ^ 59
def prefixEnd_806625 : Nat := 4983230072969 + 3 ^ 40 * 806625 * 2
def baseEnd_806625 : Nat := 368165629273788275269249

theorem tailTrace_806625 : CollatzResearch.WordTrace tailWord_806625 prefixEnd_806625 368165629273788275269249 := by
  unfold tailWord_806625
  simp only [CollatzResearch.WordTrace]
  refine ⟨29420030702742860427429329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19613353801828573618286219 29420030702742860427429329)
  ·
    refine ⟨22065023027057145320571997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29420030702742860427429329 22065023027057145320571997)
    ·
      refine ⟨8274383635146429495214499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22065023027057145320571997 8274383635146429495214499)
      ·
        refine ⟨12411575452719644242821749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8274383635146429495214499 12411575452719644242821749)
        ·
          refine ⟨1163585198692466647764539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12411575452719644242821749 1163585198692466647764539)
          ·
            refine ⟨1745377798038699971646809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163585198692466647764539 1745377798038699971646809)
            ·
              refine ⟨1309033348529024978735107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745377798038699971646809 1309033348529024978735107)
              ·
                refine ⟨1963550022793537468102661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309033348529024978735107 1963550022793537468102661)
                ·
                  refine ⟨368165629273788275269249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963550022793537468102661 368165629273788275269249)
                  ·
                    rfl

theorem cell20_806625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_806625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806625 prefixEnd_806625 := by exact prefixLift 806625
  have htrace : WordTrace (prefixWord ++ tailWord_806625) baseStart_806625 baseEnd_806625 := by
    simpa [prefixWord, tailWord_806625, baseEnd_806625] using wordTrace_append hprefix tailTrace_806625
  have hstable : (prefixWord ++ tailWord_806625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806625).length < 2 ^ (prefixWord ++ tailWord_806625).sum := by decide
  have hdescent : baseEnd_806625 < baseStart_806625 := by decide
  rcases family_descends (prefixWord ++ tailWord_806625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806662 : List Nat := [6, 2, 2, 1, 1, 2, 6]
def baseStart_806662 : Nat := 118140960795 + 806662 * 2 ^ 59
def prefixEnd_806662 : Nat := 4983230072969 + 3 ^ 40 * 806662 * 2
def baseEnd_806662 : Nat := 40909168564664510115085

theorem tailTrace_806662 : CollatzResearch.WordTrace tailWord_806662 prefixEnd_806662 40909168564664510115085 := by
  unfold tailWord_806662
  simp only [CollatzResearch.WordTrace]
  refine ⟨919418131362775492078945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19614253469072543831017493 919418131362775492078945)
  ·
    refine ⟨689563598522081619059209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 919418131362775492078945 689563598522081619059209)
    ·
      refine ⟨517172698891561214294407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 689563598522081619059209 517172698891561214294407)
      ·
        refine ⟨775759048337341821441611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517172698891561214294407 775759048337341821441611)
        ·
          refine ⟨1163638572506012732162417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775759048337341821441611 1163638572506012732162417)
          ·
            refine ⟨872728929379509549121813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163638572506012732162417 872728929379509549121813)
            ·
              refine ⟨40909168564664510115085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 872728929379509549121813 40909168564664510115085)
              ·
                rfl

theorem cell20_806662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 6].length) (baseStart_806662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806662 prefixEnd_806662 := by exact prefixLift 806662
  have htrace : WordTrace (prefixWord ++ tailWord_806662) baseStart_806662 baseEnd_806662 := by
    simpa [prefixWord, tailWord_806662, baseEnd_806662] using wordTrace_append hprefix tailTrace_806662
  have hstable : (prefixWord ++ tailWord_806662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806662).length < 2 ^ (prefixWord ++ tailWord_806662).sum := by decide
  have hdescent : baseEnd_806662 < baseStart_806662 := by decide
  rcases family_descends (prefixWord ++ tailWord_806662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806667 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_806667 : Nat := 118140960795 + 806667 * 2 ^ 59
def prefixEnd_806667 : Nat := 4983230072969 + 3 ^ 40 * 806667 * 2
def baseEnd_806667 : Nat := 368184799218222795869077

theorem tailTrace_806667 : CollatzResearch.WordTrace tailWord_806667 prefixEnd_806667 368184799218222795869077 := by
  unfold tailWord_806667
  simp only [CollatzResearch.WordTrace]
  refine ⟨29421562568590701600458255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19614375045727134400305503 29421562568590701600458255)
  ·
    refine ⟨44132343852886052400687383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29421562568590701600458255 44132343852886052400687383)
    ·
      refine ⟨66198515779329078601031075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44132343852886052400687383 66198515779329078601031075)
      ·
        refine ⟨99297773668993617901546613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66198515779329078601031075 99297773668993617901546613)
        ·
          refine ⟨9309166281468151678269995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99297773668993617901546613 9309166281468151678269995)
          ·
            refine ⟨13963749422202227517404993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9309166281468151678269995 13963749422202227517404993)
            ·
              refine ⟨10472812066651670638053745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13963749422202227517404993 10472812066651670638053745)
              ·
                refine ⟨7854609049988752978540309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10472812066651670638053745 7854609049988752978540309)
                ·
                  refine ⟨368184799218222795869077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7854609049988752978540309 368184799218222795869077)
                  ·
                    rfl

theorem cell20_806667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_806667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806667 prefixEnd_806667 := by exact prefixLift 806667
  have htrace : WordTrace (prefixWord ++ tailWord_806667) baseStart_806667 baseEnd_806667 := by
    simpa [prefixWord, tailWord_806667, baseEnd_806667] using wordTrace_append hprefix tailTrace_806667
  have hstable : (prefixWord ++ tailWord_806667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806667).length < 2 ^ (prefixWord ++ tailWord_806667).sum := by decide
  have hdescent : baseEnd_806667 < baseStart_806667 := by decide
  rcases family_descends (prefixWord ++ tailWord_806667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806676 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 4]
def baseStart_806676 : Nat := 118140960795 + 806676 * 2 ^ 59
def prefixEnd_806676 : Nat := 4983230072969 + 3 ^ 40 * 806676 * 2
def baseEnd_806676 : Nat := 368188907063458764569041

theorem tailTrace_806676 : CollatzResearch.WordTrace tailWord_806676 prefixEnd_806676 368188907063458764569041 := by
  unfold tailWord_806676
  simp only [CollatzResearch.WordTrace]
  refine ⟨14710945412779048068767941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19614593883705397425023921 14710945412779048068767941)
  ·
    refine ⟨2758302264896071512893989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14710945412779048068767941 2758302264896071512893989)
    ·
      refine ⟨517181674668013408667623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2758302264896071512893989 517181674668013408667623)
      ·
        refine ⟨775772512002020113001435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517181674668013408667623 775772512002020113001435)
        ·
          refine ⟨1163658768003030169502153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775772512002020113001435 1163658768003030169502153)
          ·
            refine ⟨872744076002272627126615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163658768003030169502153 872744076002272627126615)
            ·
              refine ⟨1309116114003408940689923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872744076002272627126615 1309116114003408940689923)
              ·
                refine ⟨1963674171005113411034885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309116114003408940689923 1963674171005113411034885)
                ·
                  refine ⟨368188907063458764569041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963674171005113411034885 368188907063458764569041)
                  ·
                    rfl

theorem cell20_806676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_806676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806676 prefixEnd_806676 := by exact prefixLift 806676
  have htrace : WordTrace (prefixWord ++ tailWord_806676) baseStart_806676 baseEnd_806676 := by
    simpa [prefixWord, tailWord_806676, baseEnd_806676] using wordTrace_append hprefix tailTrace_806676
  have hstable : (prefixWord ++ tailWord_806676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806676).length < 2 ^ (prefixWord ++ tailWord_806676).sum := by decide
  have hdescent : baseEnd_806676 < baseStart_806676 := by decide
  rcases family_descends (prefixWord ++ tailWord_806676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806686 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_806686 : Nat := 118140960795 + 806686 * 2 ^ 59
def prefixEnd_806686 : Nat := 4983230072969 + 3 ^ 40 * 806686 * 2
def baseEnd_806686 : Nat := 368193471335943174235667

theorem tailTrace_806686 : CollatzResearch.WordTrace tailWord_806686 prefixEnd_806686 368193471335943174235667 := by
  unfold tailWord_806686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677781944440233480674989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19614837037014578563599941 3677781944440233480674989)
  ·
    refine ⟨1379168229165087555253121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3677781944440233480674989 1379168229165087555253121)
    ·
      refine ⟨1034376171873815666439841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1379168229165087555253121 1034376171873815666439841)
      ·
        refine ⟨775782128905361749829881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1034376171873815666439841 775782128905361749829881)
        ·
          refine ⟨581836596679021312372411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775782128905361749829881 581836596679021312372411)
          ·
            refine ⟨872754895018531968558617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581836596679021312372411 872754895018531968558617)
            ·
              refine ⟨654566171263898976418963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872754895018531968558617 654566171263898976418963)
              ·
                refine ⟨981849256895848464628445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654566171263898976418963 981849256895848464628445)
                ·
                  refine ⟨368193471335943174235667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981849256895848464628445 368193471335943174235667)
                  ·
                    rfl

theorem cell20_806686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_806686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806686 prefixEnd_806686 := by exact prefixLift 806686
  have htrace : WordTrace (prefixWord ++ tailWord_806686) baseStart_806686 baseEnd_806686 := by
    simpa [prefixWord, tailWord_806686, baseEnd_806686] using wordTrace_append hprefix tailTrace_806686
  have hstable : (prefixWord ++ tailWord_806686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806686).length < 2 ^ (prefixWord ++ tailWord_806686).sum := by decide
  have hdescent : baseEnd_806686 < baseStart_806686 := by decide
  rcases family_descends (prefixWord ++ tailWord_806686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806708 : List Nat := [2, 5, 1, 1, 2, 1, 2, 6]
def baseStart_806708 : Nat := 118140960795 + 806708 * 2 ^ 59
def prefixEnd_806708 : Nat := 4983230072969 + 3 ^ 40 * 806708 * 2
def baseEnd_806708 : Nat := 122734504245136291834081

theorem tailTrace_806708 : CollatzResearch.WordTrace tailWord_806708 prefixEnd_806708 122734504245136291834081 := by
  unfold tailWord_806708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711528980721082801350389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19615371974294777068467185 14711528980721082801350389)
  ·
    refine ⟨1379205841942601512626599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14711528980721082801350389 1379205841942601512626599)
    ·
      refine ⟨2068808762913902268939899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379205841942601512626599 2068808762913902268939899)
      ·
        refine ⟨3103213144370853403409849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068808762913902268939899 3103213144370853403409849)
        ·
          refine ⟨2327409858278140052557387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3103213144370853403409849 2327409858278140052557387)
          ·
            refine ⟨3491114787417210078836081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327409858278140052557387 3491114787417210078836081)
            ·
              refine ⟨2618336090562907559127061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3491114787417210078836081 2618336090562907559127061)
              ·
                refine ⟨122734504245136291834081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2618336090562907559127061 122734504245136291834081)
                ·
                  rfl

theorem cell20_806708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_806708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806708 prefixEnd_806708 := by exact prefixLift 806708
  have htrace : WordTrace (prefixWord ++ tailWord_806708) baseStart_806708 baseEnd_806708 := by
    simpa [prefixWord, tailWord_806708, baseEnd_806708] using wordTrace_append hprefix tailTrace_806708
  have hstable : (prefixWord ++ tailWord_806708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806708).length < 2 ^ (prefixWord ++ tailWord_806708).sum := by decide
  have hdescent : baseEnd_806708 < baseStart_806708 := by decide
  rcases family_descends (prefixWord ++ tailWord_806708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806732 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_806732 : Nat := 118140960795 + 806732 * 2 ^ 59
def prefixEnd_806732 : Nat := 4983230072969 + 3 ^ 40 * 806732 * 2
def baseEnd_806732 : Nat := 368214466989371458702145

theorem tailTrace_806732 : CollatzResearch.WordTrace tailWord_806732 prefixEnd_806732 368214466989371458702145 := by
  unfold tailWord_806732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711966656677608850787225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19615955542236811801049633 14711966656677608850787225)
  ·
    refine ⟨11033974992508206638090419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14711966656677608850787225 11033974992508206638090419)
    ·
      refine ⟨16550962488762309957135629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11033974992508206638090419 16550962488762309957135629)
      ·
        refine ⟨6206610933285866233925861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16550962488762309957135629 6206610933285866233925861)
        ·
          refine ⟨1163739549991099918861099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6206610933285866233925861 1163739549991099918861099)
          ·
            refine ⟨1745609324986649878291649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163739549991099918861099 1745609324986649878291649)
            ·
              refine ⟨1309206993739987408718737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745609324986649878291649 1309206993739987408718737)
              ·
                refine ⟨981905245304990556539053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309206993739987408718737 981905245304990556539053)
                ·
                  refine ⟨368214466989371458702145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981905245304990556539053 368214466989371458702145)
                  ·
                    rfl

theorem cell20_806732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_806732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806732 prefixEnd_806732 := by exact prefixLift 806732
  have htrace : WordTrace (prefixWord ++ tailWord_806732) baseStart_806732 baseEnd_806732 := by
    simpa [prefixWord, tailWord_806732, baseEnd_806732] using wordTrace_append hprefix tailTrace_806732
  have hstable : (prefixWord ++ tailWord_806732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806732).length < 2 ^ (prefixWord ++ tailWord_806732).sum := by decide
  have hdescent : baseEnd_806732 < baseStart_806732 := by decide
  rcases family_descends (prefixWord ++ tailWord_806732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806760 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_806760 : Nat := 118140960795 + 806760 * 2 ^ 59
def prefixEnd_806760 : Nat := 4983230072969 + 3 ^ 40 * 806760 * 2
def baseEnd_806760 : Nat := 368227246952327805768697

theorem tailTrace_806760 : CollatzResearch.WordTrace tailWord_806760 prefixEnd_806760 368227246952327805768697 := by
  unfold tailWord_806760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14712477278626889241796867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19616636371502518989062489 14712477278626889241796867)
  ·
    refine ⟨22068715917940333862695301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14712477278626889241796867 22068715917940333862695301)
    ·
      refine ⟨4137884234613812599255369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22068715917940333862695301 4137884234613812599255369)
      ·
        refine ⟨3103413175960359449441527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4137884234613812599255369 3103413175960359449441527)
        ·
          refine ⟨4655119763940539174162291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103413175960359449441527 4655119763940539174162291)
          ·
            refine ⟨6982679645910808761243437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4655119763940539174162291 6982679645910808761243437)
            ·
              refine ⟨2618504867216553285466289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6982679645910808761243437 2618504867216553285466289)
              ·
                refine ⟨1963878650412414964099717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618504867216553285466289 1963878650412414964099717)
                ·
                  refine ⟨368227246952327805768697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1963878650412414964099717 368227246952327805768697)
                  ·
                    rfl

theorem cell20_806760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_806760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806760 prefixEnd_806760 := by exact prefixLift 806760
  have htrace : WordTrace (prefixWord ++ tailWord_806760) baseStart_806760 baseEnd_806760 := by
    simpa [prefixWord, tailWord_806760, baseEnd_806760] using wordTrace_append hprefix tailTrace_806760
  have hstable : (prefixWord ++ tailWord_806760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806760).length < 2 ^ (prefixWord ++ tailWord_806760).sum := by decide
  have hdescent : baseEnd_806760 < baseStart_806760 := by decide
  rcases family_descends (prefixWord ++ tailWord_806760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806777 : List Nat := [1, 2, 1, 3, 2, 2, 4, 3, 2]
def baseStart_806777 : Nat := 118140960795 + 806777 * 2 ^ 59
def prefixEnd_806777 : Nat := 4983230072969 + 3 ^ 40 * 806777 * 2
def baseEnd_806777 : Nat := 368235006215551302201961

theorem tailTrace_806777 : CollatzResearch.WordTrace tailWord_806777 prefixEnd_806777 368235006215551302201961 := by
  unfold tailWord_806777
  simp only [CollatzResearch.WordTrace]
  refine ⟨29425574598192190386962585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19617049732128126924641723 29425574598192190386962585)
  ·
    refine ⟨22069180948644142790221939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29425574598192190386962585 22069180948644142790221939)
    ·
      refine ⟨33103771422966214185332909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22069180948644142790221939 33103771422966214185332909)
      ·
        refine ⟨12413914283612330319499841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33103771422966214185332909 12413914283612330319499841)
        ·
          refine ⟨9310435712709247739624881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12413914283612330319499841 9310435712709247739624881)
          ·
            refine ⟨6982826784531935804718661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9310435712709247739624881 6982826784531935804718661)
            ·
              refine ⟨1309280022099737963384749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6982826784531935804718661 1309280022099737963384749)
              ·
                refine ⟨490980008287401736269281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1309280022099737963384749 490980008287401736269281)
                ·
                  refine ⟨368235006215551302201961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490980008287401736269281 368235006215551302201961)
                  ·
                    rfl

theorem cell20_806777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_806777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806777 prefixEnd_806777 := by exact prefixLift 806777
  have htrace : WordTrace (prefixWord ++ tailWord_806777) baseStart_806777 baseEnd_806777 := by
    simpa [prefixWord, tailWord_806777, baseEnd_806777] using wordTrace_append hprefix tailTrace_806777
  have hstable : (prefixWord ++ tailWord_806777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806777).length < 2 ^ (prefixWord ++ tailWord_806777).sum := by decide
  have hdescent : baseEnd_806777 < baseStart_806777 := by decide
  rcases family_descends (prefixWord ++ tailWord_806777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806781 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_806781 : Nat := 118140960795 + 806781 * 2 ^ 59
def prefixEnd_806781 : Nat := 4983230072969 + 3 ^ 40 * 806781 * 2
def baseEnd_806781 : Nat := 368236831924545066068611

theorem tailTrace_806781 : CollatzResearch.WordTrace tailWord_806781 prefixEnd_806781 368236831924545066068611 := by
  unfold tailWord_806781
  simp only [CollatzResearch.WordTrace]
  refine ⟨29425720490177699070108197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19617146993451799380072131 29425720490177699070108197)
  ·
    refine ⟨5517322591908318575645287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29425720490177699070108197 5517322591908318575645287)
    ·
      refine ⟨8275983887862477863467931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5517322591908318575645287 8275983887862477863467931)
      ·
        refine ⟨12413975831793716795201897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8275983887862477863467931 12413975831793716795201897)
        ·
          refine ⟨9310481873845287596401423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12413975831793716795201897 9310481873845287596401423)
          ·
            refine ⟨13965722810767931394602135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9310481873845287596401423 13965722810767931394602135)
            ·
              refine ⟨20948584216151897091903203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13965722810767931394602135 20948584216151897091903203)
              ·
                refine ⟨31422876324227845637854805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20948584216151897091903203 31422876324227845637854805)
                ·
                  refine ⟨368236831924545066068611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31422876324227845637854805 368236831924545066068611)
                  ·
                    rfl

theorem cell20_806781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_806781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806781 prefixEnd_806781 := by exact prefixLift 806781
  have htrace : WordTrace (prefixWord ++ tailWord_806781) baseStart_806781 baseEnd_806781 := by
    simpa [prefixWord, tailWord_806781, baseEnd_806781] using wordTrace_append hprefix tailTrace_806781
  have hstable : (prefixWord ++ tailWord_806781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806781).length < 2 ^ (prefixWord ++ tailWord_806781).sum := by decide
  have hdescent : baseEnd_806781 < baseStart_806781 := by decide
  rcases family_descends (prefixWord ++ tailWord_806781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806791 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 5]
def baseStart_806791 : Nat := 118140960795 + 806791 * 2 ^ 59
def prefixEnd_806791 : Nat := 4983230072969 + 3 ^ 40 * 806791 * 2
def baseEnd_806791 : Nat := 368241396197029475735237

theorem tailTrace_806791 : CollatzResearch.WordTrace tailWord_806791 prefixEnd_806791 368241396197029475735237 := by
  unfold tailWord_806791
  simp only [CollatzResearch.WordTrace]
  refine ⟨29426085220141470777972227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19617390146760980518648151 29426085220141470777972227)
  ·
    refine ⟨44139127830212206166958341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29426085220141470777972227 44139127830212206166958341)
    ·
      refine ⟨8276086468164788656304689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44139127830212206166958341 8276086468164788656304689)
      ·
        refine ⟨6207064851123591492228517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8276086468164788656304689 6207064851123591492228517)
        ·
          refine ⟨1163824659585673404792847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6207064851123591492228517 1163824659585673404792847)
          ·
            refine ⟨1745736989378510107189271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163824659585673404792847 1745736989378510107189271)
            ·
              refine ⟨2618605484067765160783907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745736989378510107189271 2618605484067765160783907)
              ·
                refine ⟨3927908226101647741175861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618605484067765160783907 3927908226101647741175861)
                ·
                  refine ⟨368241396197029475735237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927908226101647741175861 368241396197029475735237)
                  ·
                    rfl

theorem cell20_806791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_806791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806791 prefixEnd_806791 := by exact prefixLift 806791
  have htrace : WordTrace (prefixWord ++ tailWord_806791) baseStart_806791 baseEnd_806791 := by
    simpa [prefixWord, tailWord_806791, baseEnd_806791] using wordTrace_append hprefix tailTrace_806791
  have hstable : (prefixWord ++ tailWord_806791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806791).length < 2 ^ (prefixWord ++ tailWord_806791).sum := by decide
  have hdescent : baseEnd_806791 < baseStart_806791 := by decide
  rcases family_descends (prefixWord ++ tailWord_806791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806818 : List Nat := [3, 3, 1, 2, 4, 1, 2, 4]
def baseStart_806818 : Nat := 118140960795 + 806818 * 2 ^ 59
def prefixEnd_806818 : Nat := 4983230072969 + 3 ^ 40 * 806818 * 2
def baseEnd_806818 : Nat := 122751239910912460611709

theorem tailTrace_806818 : CollatzResearch.WordTrace tailWord_806818 prefixEnd_806818 122751239910912460611709 := by
  unfold tailWord_806818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356767497760913597301277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19618046660695769592803405 7356767497760913597301277)
  ·
    refine ⟨2758787811660342598987979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7356767497760913597301277 2758787811660342598987979)
    ·
      refine ⟨4138181717490513898481969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2758787811660342598987979 4138181717490513898481969)
      ·
        refine ⟨3103636288117885423861477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4138181717490513898481969 3103636288117885423861477)
        ·
          refine ⟨581931804022103516974027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3103636288117885423861477 581931804022103516974027)
          ·
            refine ⟨872897706033155275461041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581931804022103516974027 872897706033155275461041)
            ·
              refine ⟨654673279524866456595781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872897706033155275461041 654673279524866456595781)
              ·
                refine ⟨122751239910912460611709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654673279524866456595781 122751239910912460611709)
                ·
                  rfl

theorem cell20_806818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_806818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806818 prefixEnd_806818 := by exact prefixLift 806818
  have htrace : WordTrace (prefixWord ++ tailWord_806818) baseStart_806818 baseEnd_806818 := by
    simpa [prefixWord, tailWord_806818, baseEnd_806818] using wordTrace_append hprefix tailTrace_806818
  have hstable : (prefixWord ++ tailWord_806818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806818).length < 2 ^ (prefixWord ++ tailWord_806818).sum := by decide
  have hdescent : baseEnd_806818 < baseStart_806818 := by decide
  rcases family_descends (prefixWord ++ tailWord_806818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806864 : List Nat := [2, 1, 1, 1, 1, 2, 5, 7]
def baseStart_806864 : Nat := 118140960795 + 806864 * 2 ^ 59
def prefixEnd_806864 : Nat := 4983230072969 + 3 ^ 40 * 806864 * 2
def baseEnd_806864 : Nat := 122758238462055222100535

theorem tailTrace_806864 : CollatzResearch.WordTrace tailWord_806864 prefixEnd_806864 122758238462055222100535 := by
  unfold tailWord_806864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14714373874438502122689823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19619165165918002830253097 14714373874438502122689823)
  ·
    refine ⟨22071560811657753184034735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14714373874438502122689823 22071560811657753184034735)
    ·
      refine ⟨33107341217486629776052103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22071560811657753184034735 33107341217486629776052103)
      ·
        refine ⟨49661011826229944664078155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33107341217486629776052103 49661011826229944664078155)
        ·
          refine ⟨74491517739344916996117233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49661011826229944664078155 74491517739344916996117233)
          ·
            refine ⟨55868638304508687747087925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74491517739344916996117233 55868638304508687747087925)
            ·
              refine ⟨5237684841047689476289493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55868638304508687747087925 5237684841047689476289493)
              ·
                refine ⟨122758238462055222100535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5237684841047689476289493 122758238462055222100535)
                ·
                  rfl

theorem cell20_806864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_806864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806864 prefixEnd_806864 := by exact prefixLift 806864
  have htrace : WordTrace (prefixWord ++ tailWord_806864) baseStart_806864 baseEnd_806864 := by
    simpa [prefixWord, tailWord_806864, baseEnd_806864] using wordTrace_append hprefix tailTrace_806864
  have hstable : (prefixWord ++ tailWord_806864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806864).length < 2 ^ (prefixWord ++ tailWord_806864).sum := by decide
  have hdescent : baseEnd_806864 < baseStart_806864 := by decide
  rcases family_descends (prefixWord ++ tailWord_806864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806905 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 3]
def baseStart_806905 : Nat := 118140960795 + 806905 * 2 ^ 59
def prefixEnd_806905 : Nat := 4983230072969 + 3 ^ 40 * 806905 * 2
def baseEnd_806905 : Nat := 368293428903351745934771

theorem tailTrace_806905 : CollatzResearch.WordTrace tailWord_806905 prefixEnd_806905 368293428903351745934771 := by
  unfold tailWord_806905
  simp only [CollatzResearch.WordTrace]
  refine ⟨29430243141728468247622169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19620162094485645498414779 29430243141728468247622169)
  ·
    refine ⟨22072682356296351185716627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29430243141728468247622169 22072682356296351185716627)
    ·
      refine ⟨33109023534444526778574941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22072682356296351185716627 33109023534444526778574941)
      ·
        refine ⟨12415883825416697541965603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33109023534444526778574941 12415883825416697541965603)
        ·
          refine ⟨18623825738125046312948405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12415883825416697541965603 18623825738125046312948405)
          ·
            refine ⟨1745983662949223091838913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18623825738125046312948405 1745983662949223091838913)
            ·
              refine ⟨1309487747211917318879185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745983662949223091838913 1309487747211917318879185)
              ·
                refine ⟨982115810408937989159389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309487747211917318879185 982115810408937989159389)
                ·
                  refine ⟨368293428903351745934771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982115810408937989159389 368293428903351745934771)
                  ·
                    rfl

theorem cell20_806905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_806905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806905 prefixEnd_806905 := by exact prefixLift 806905
  have htrace : WordTrace (prefixWord ++ tailWord_806905) baseStart_806905 baseEnd_806905 := by
    simpa [prefixWord, tailWord_806905, baseEnd_806905] using wordTrace_append hprefix tailTrace_806905
  have hstable : (prefixWord ++ tailWord_806905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806905).length < 2 ^ (prefixWord ++ tailWord_806905).sum := by decide
  have hdescent : baseEnd_806905 < baseStart_806905 := by decide
  rcases family_descends (prefixWord ++ tailWord_806905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806919 : List Nat := [1, 1, 4, 3, 1, 2, 3, 5]
def baseStart_806919 : Nat := 118140960795 + 806919 * 2 ^ 59
def prefixEnd_806919 : Nat := 4983230072969 + 3 ^ 40 * 806919 * 2
def baseEnd_806919 : Nat := 122766606294943306489349

theorem tailTrace_806919 : CollatzResearch.WordTrace tailWord_806919 prefixEnd_806919 122766606294943306489349 := by
  unfold tailWord_806919
  simp only [CollatzResearch.WordTrace]
  refine ⟨29430753763677748638631811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19620502509118499092421207 29430753763677748638631811)
  ·
    refine ⟨44146130645516622957947717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29430753763677748638631811 44146130645516622957947717)
    ·
      refine ⟨8277399496034366804615197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44146130645516622957947717 8277399496034366804615197)
      ·
        refine ⟨3104024811012887551730699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8277399496034366804615197 3104024811012887551730699)
        ·
          refine ⟨4656037216519331327596049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104024811012887551730699 4656037216519331327596049)
          ·
            refine ⟨3492027912389498495697037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4656037216519331327596049 3492027912389498495697037)
            ·
              refine ⟨1309510467146061935886389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3492027912389498495697037 1309510467146061935886389)
              ·
                refine ⟨122766606294943306489349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1309510467146061935886389 122766606294943306489349)
                ·
                  rfl

theorem cell20_806919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_806919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806919 prefixEnd_806919 := by exact prefixLift 806919
  have htrace : WordTrace (prefixWord ++ tailWord_806919) baseStart_806919 baseEnd_806919 := by
    simpa [prefixWord, tailWord_806919, baseEnd_806919] using wordTrace_append hprefix tailTrace_806919
  have hstable : (prefixWord ++ tailWord_806919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806919).length < 2 ^ (prefixWord ++ tailWord_806919).sum := by decide
  have hdescent : baseEnd_806919 < baseStart_806919 := by decide
  rcases family_descends (prefixWord ++ tailWord_806919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806925 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 4]
def baseStart_806925 : Nat := 118140960795 + 806925 * 2 ^ 59
def prefixEnd_806925 : Nat := 4983230072969 + 3 ^ 40 * 806925 * 2
def baseEnd_806925 : Nat := 368302557448320565268023

theorem tailTrace_806925 : CollatzResearch.WordTrace tailWord_806925 prefixEnd_806925 368302557448320565268023 := by
  unfold tailWord_806925
  simp only [CollatzResearch.WordTrace]
  refine ⟨29430972601656011663350229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19620648401104007775566819 29430972601656011663350229)
  ·
    refine ⟨689788420351312773359771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29430972601656011663350229 689788420351312773359771)
    ·
      refine ⟨1034682630526969160039657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689788420351312773359771 1034682630526969160039657)
      ·
        refine ⟨776011972895226870029743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1034682630526969160039657 776011972895226870029743)
        ·
          refine ⟨1164017959342840305044615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776011972895226870029743 1164017959342840305044615)
          ·
            refine ⟨1746026939014260457566923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164017959342840305044615 1746026939014260457566923)
            ·
              refine ⟨2619040408521390686350385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746026939014260457566923 2619040408521390686350385)
              ·
                refine ⟨1964280306391043014762789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619040408521390686350385 1964280306391043014762789)
                ·
                  refine ⟨368302557448320565268023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964280306391043014762789 368302557448320565268023)
                  ·
                    rfl

theorem cell20_806925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_806925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806925 prefixEnd_806925 := by exact prefixLift 806925
  have htrace : WordTrace (prefixWord ++ tailWord_806925) baseStart_806925 baseEnd_806925 := by
    simpa [prefixWord, tailWord_806925, baseEnd_806925] using wordTrace_append hprefix tailTrace_806925
  have hstable : (prefixWord ++ tailWord_806925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806925).length < 2 ^ (prefixWord ++ tailWord_806925).sum := by decide
  have hdescent : baseEnd_806925 < baseStart_806925 := by decide
  rcases family_descends (prefixWord ++ tailWord_806925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806932 : List Nat := [2, 4, 3, 2, 1, 1, 3, 4]
def baseStart_806932 : Nat := 118140960795 + 806932 * 2 ^ 59
def prefixEnd_806932 : Nat := 4983230072969 + 3 ^ 40 * 806932 * 2
def baseEnd_806932 : Nat := 122768584146353217344887

theorem tailTrace_806932 : CollatzResearch.WordTrace tailWord_806932 prefixEnd_806932 122768584146353217344887 := by
  unfold tailWord_806932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14715613956315325929427525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19620818608420434572570033 14715613956315325929427525)
  ·
    refine ⟨2759177616809123611767661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14715613956315325929427525 2759177616809123611767661)
    ·
      refine ⟨1034691606303421354412873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2759177616809123611767661 1034691606303421354412873)
      ·
        refine ⟨776018704727566015809655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1034691606303421354412873 776018704727566015809655)
        ·
          refine ⟨1164028057091349023714483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776018704727566015809655 1164028057091349023714483)
          ·
            refine ⟨1746042085637023535571725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164028057091349023714483 1746042085637023535571725)
            ·
              refine ⟨654765782113883825839397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1746042085637023535571725 654765782113883825839397)
              ·
                refine ⟨122768584146353217344887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654765782113883825839397 122768584146353217344887)
                ·
                  rfl

theorem cell20_806932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_806932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806932 prefixEnd_806932 := by exact prefixLift 806932
  have htrace : WordTrace (prefixWord ++ tailWord_806932) baseStart_806932 baseEnd_806932 := by
    simpa [prefixWord, tailWord_806932, baseEnd_806932] using wordTrace_append hprefix tailTrace_806932
  have hstable : (prefixWord ++ tailWord_806932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806932).length < 2 ^ (prefixWord ++ tailWord_806932).sum := by decide
  have hdescent : baseEnd_806932 < baseStart_806932 := by decide
  rcases family_descends (prefixWord ++ tailWord_806932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806998 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_806998 : Nat := 118140960795 + 806998 * 2 ^ 59
def prefixEnd_806998 : Nat := 4983230072969 + 3 ^ 40 * 806998 * 2
def baseEnd_806998 : Nat := 368335876637456755834391

theorem tailTrace_806998 : CollatzResearch.WordTrace tailWord_806998 prefixEnd_806998 368335876637456755834391 := by
  unfold tailWord_806998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839602195649471570672353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19622423420261030087171765 1839602195649471570672353)
  ·
    refine ⟨1379701646737103678004265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839602195649471570672353 1379701646737103678004265)
    ·
      refine ⟨1034776235052827758503199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1379701646737103678004265 1034776235052827758503199)
      ·
        refine ⟨1552164352579241637754799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034776235052827758503199 1552164352579241637754799)
        ·
          refine ⟨2328246528868862456632199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552164352579241637754799 2328246528868862456632199)
          ·
            refine ⟨3492369793303293684948299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328246528868862456632199 3492369793303293684948299)
            ·
              refine ⟨5238554689954940527422449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492369793303293684948299 5238554689954940527422449)
              ·
                refine ⟨3928916017466205395566837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238554689954940527422449 3928916017466205395566837)
                ·
                  refine ⟨368335876637456755834391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3928916017466205395566837 368335876637456755834391)
                  ·
                    rfl

theorem cell20_806998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_806998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_806998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_806998 prefixEnd_806998 := by exact prefixLift 806998
  have htrace : WordTrace (prefixWord ++ tailWord_806998) baseStart_806998 baseEnd_806998 := by
    simpa [prefixWord, tailWord_806998, baseEnd_806998] using wordTrace_append hprefix tailTrace_806998
  have hstable : (prefixWord ++ tailWord_806998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806998).length < 2 ^ (prefixWord ++ tailWord_806998).sum := by decide
  have hdescent : baseEnd_806998 < baseStart_806998 := by decide
  rcases family_descends (prefixWord ++ tailWord_806998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807022 : List Nat := [4, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_807022 : Nat := 118140960795 + 807022 * 2 ^ 59
def prefixEnd_807022 : Nat := 4983230072969 + 3 ^ 40 * 807022 * 2
def baseEnd_807022 : Nat := 368346830891419339034293

theorem tailTrace_807022 : CollatzResearch.WordTrace tailWord_807022 prefixEnd_807022 368346830891419339034293 := by
  unfold tailWord_807022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679313810288074653703915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19623006988203064819754213 3679313810288074653703915)
  ·
    refine ⟨5518970715432111980555873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3679313810288074653703915 5518970715432111980555873)
    ·
      refine ⟨4139228036574083985416905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5518970715432111980555873 4139228036574083985416905)
      ·
        refine ⟨3104421027430562989062679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4139228036574083985416905 3104421027430562989062679)
        ·
          refine ⟨4656631541145844483594019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104421027430562989062679 4656631541145844483594019)
          ·
            refine ⟨6984947311718766725391029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656631541145844483594019 6984947311718766725391029)
            ·
              refine ⟨654838810473634380505409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6984947311718766725391029 654838810473634380505409)
              ·
                refine ⟨491129107855225785379057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654838810473634380505409 491129107855225785379057)
                ·
                  refine ⟨368346830891419339034293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491129107855225785379057 368346830891419339034293)
                  ·
                    rfl

theorem cell20_807022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_807022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807022 prefixEnd_807022 := by exact prefixLift 807022
  have htrace : WordTrace (prefixWord ++ tailWord_807022) baseStart_807022 baseEnd_807022 := by
    simpa [prefixWord, tailWord_807022, baseEnd_807022] using wordTrace_append hprefix tailTrace_807022
  have hstable : (prefixWord ++ tailWord_807022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807022).length < 2 ^ (prefixWord ++ tailWord_807022).sum := by decide
  have hdescent : baseEnd_807022 < baseStart_807022 := by decide
  rcases family_descends (prefixWord ++ tailWord_807022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807026 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_807026 : Nat := 118140960795 + 807026 * 2 ^ 59
def prefixEnd_807026 : Nat := 4983230072969 + 3 ^ 40 * 807026 * 2
def baseEnd_807026 : Nat := 368348656600413102900943

theorem tailTrace_807026 : CollatzResearch.WordTrace tailWord_807026 prefixEnd_807026 368348656600413102900943 := by
  unfold tailWord_807026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358664093572526478194233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19623104249526737275184621 7358664093572526478194233)
  ·
    refine ⟨5518998070179394858645675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7358664093572526478194233 5518998070179394858645675)
    ·
      refine ⟨8278497105269092287968513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518998070179394858645675 8278497105269092287968513)
      ·
        refine ⟨6208872828951819215976385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8278497105269092287968513 6208872828951819215976385)
        ·
          refine ⟨4656654621713864411982289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6208872828951819215976385 4656654621713864411982289)
          ·
            refine ⟨3492490966285398308986717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4656654621713864411982289 3492490966285398308986717)
            ·
              refine ⟨1309684112357024365870019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3492490966285398308986717 1309684112357024365870019)
              ·
                refine ⟨1964526168535536548805029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309684112357024365870019 1964526168535536548805029)
                ·
                  refine ⟨368348656600413102900943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964526168535536548805029 368348656600413102900943)
                  ·
                    rfl

theorem cell20_807026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_807026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807026 prefixEnd_807026 := by exact prefixLift 807026
  have htrace : WordTrace (prefixWord ++ tailWord_807026) baseStart_807026 baseEnd_807026 := by
    simpa [prefixWord, tailWord_807026, baseEnd_807026] using wordTrace_append hprefix tailTrace_807026
  have hstable : (prefixWord ++ tailWord_807026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807026).length < 2 ^ (prefixWord ++ tailWord_807026).sum := by decide
  have hdescent : baseEnd_807026 < baseStart_807026 := by decide
  rcases family_descends (prefixWord ++ tailWord_807026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807033 : List Nat := [1, 2, 1, 3, 4, 2, 2, 5]
def baseStart_807033 : Nat := 118140960795 + 807033 * 2 ^ 59
def prefixEnd_807033 : Nat := 4983230072969 + 3 ^ 40 * 807033 * 2
def baseEnd_807033 : Nat := 122783950530384063222527

theorem tailTrace_807033 : CollatzResearch.WordTrace tailWord_807033 prefixEnd_807033 122783950530384063222527 := by
  unfold tailWord_807033
  simp only [CollatzResearch.WordTrace]
  refine ⟨29434911685264746108281753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19623274456843164072187835 29434911685264746108281753)
  ·
    refine ⟨22076183763948559581211315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29434911685264746108281753 22076183763948559581211315)
    ·
      refine ⟨33114275645922839371816973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22076183763948559581211315 33114275645922839371816973)
      ·
        refine ⟨12417853367221064764431365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33114275645922839371816973 12417853367221064764431365)
        ·
          refine ⟨2328347506353949643330881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12417853367221064764431365 2328347506353949643330881)
          ·
            refine ⟨1746260629765462232498161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328347506353949643330881 1746260629765462232498161)
            ·
              refine ⟨1309695472324096674373621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746260629765462232498161 1309695472324096674373621)
              ·
                refine ⟨122783950530384063222527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1309695472324096674373621 122783950530384063222527)
                ·
                  rfl

theorem cell20_807033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_807033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807033 prefixEnd_807033 := by exact prefixLift 807033
  have htrace : WordTrace (prefixWord ++ tailWord_807033) baseStart_807033 baseEnd_807033 := by
    simpa [prefixWord, tailWord_807033, baseEnd_807033] using wordTrace_append hprefix tailTrace_807033
  have hstable : (prefixWord ++ tailWord_807033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807033).length < 2 ^ (prefixWord ++ tailWord_807033).sum := by decide
  have hdescent : baseEnd_807033 < baseStart_807033 := by decide
  rcases family_descends (prefixWord ++ tailWord_807033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807036 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_807036 : Nat := 118140960795 + 807036 * 2 ^ 59
def prefixEnd_807036 : Nat := 4983230072969 + 3 ^ 40 * 807036 * 2
def baseEnd_807036 : Nat := 368353220872897512567569

theorem tailTrace_807036 : CollatzResearch.WordTrace tailWord_807036 prefixEnd_807036 368353220872897512567569 := by
  unfold tailWord_807036
  simp only [CollatzResearch.WordTrace]
  refine ⟨14717510552126938810320481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19623347402835918413760641 14717510552126938810320481)
  ·
    refine ⟨11038132914095204107740361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14717510552126938810320481 11038132914095204107740361)
    ·
      refine ⟨8278599685571403080805271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11038132914095204107740361 8278599685571403080805271)
      ·
        refine ⟨12417899528357104621207907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8278599685571403080805271 12417899528357104621207907)
        ·
          refine ⟨18626849292535656931811861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12417899528357104621207907 18626849292535656931811861)
          ·
            refine ⟨873133560587608918678681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18626849292535656931811861 873133560587608918678681)
            ·
              refine ⟨654850170440706689009011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873133560587608918678681 654850170440706689009011)
              ·
                refine ⟨982275255661060033513517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654850170440706689009011 982275255661060033513517)
                ·
                  refine ⟨368353220872897512567569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982275255661060033513517 368353220872897512567569)
                  ·
                    rfl

theorem cell20_807036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_807036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807036 prefixEnd_807036 := by exact prefixLift 807036
  have htrace : WordTrace (prefixWord ++ tailWord_807036) baseStart_807036 baseEnd_807036 := by
    simpa [prefixWord, tailWord_807036, baseEnd_807036] using wordTrace_append hprefix tailTrace_807036
  have hstable : (prefixWord ++ tailWord_807036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807036).length < 2 ^ (prefixWord ++ tailWord_807036).sum := by decide
  have hdescent : baseEnd_807036 < baseStart_807036 := by decide
  rcases family_descends (prefixWord ++ tailWord_807036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807047 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_807047 : Nat := 118140960795 + 807047 * 2 ^ 59
def prefixEnd_807047 : Nat := 4983230072969 + 3 ^ 40 * 807047 * 2
def baseEnd_807047 : Nat := 368358241572630363200857

theorem tailTrace_807047 : CollatzResearch.WordTrace tailWord_807047 prefixEnd_807047 368358241572630363200857 := by
  unfold tailWord_807047
  simp only [CollatzResearch.WordTrace]
  refine ⟨29435422307214026499291395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19623614871476017666194263 29435422307214026499291395)
  ·
    refine ⟨44153133460821039748937093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29435422307214026499291395 44153133460821039748937093)
    ·
      refine ⟨8278712523903944952925705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44153133460821039748937093 8278712523903944952925705)
      ·
        refine ⟨6209034392927958714694279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8278712523903944952925705 6209034392927958714694279)
        ·
          refine ⟨9313551589391938072041419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209034392927958714694279 9313551589391938072041419)
          ·
            refine ⟨13970327384087907108062129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9313551589391938072041419 13970327384087907108062129)
            ·
              refine ⟨10477745538065930331046597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13970327384087907108062129 10477745538065930331046597)
              ·
                refine ⟨1964577288387361937071237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10477745538065930331046597 1964577288387361937071237)
                ·
                  refine ⟨368358241572630363200857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964577288387361937071237 368358241572630363200857)
                  ·
                    rfl

theorem cell20_807047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_807047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807047 prefixEnd_807047 := by exact prefixLift 807047
  have htrace : WordTrace (prefixWord ++ tailWord_807047) baseStart_807047 baseEnd_807047 := by
    simpa [prefixWord, tailWord_807047, baseEnd_807047] using wordTrace_append hprefix tailTrace_807047
  have hstable : (prefixWord ++ tailWord_807047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807047).length < 2 ^ (prefixWord ++ tailWord_807047).sum := by decide
  have hdescent : baseEnd_807047 < baseStart_807047 := by decide
  rcases family_descends (prefixWord ++ tailWord_807047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807074 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_807074 : Nat := 118140960795 + 807074 * 2 ^ 59
def prefixEnd_807074 : Nat := 4983230072969 + 3 ^ 40 * 807074 * 2
def baseEnd_807074 : Nat := 368370565108338269300747

theorem tailTrace_807074 : CollatzResearch.WordTrace tailWord_807074 prefixEnd_807074 368370565108338269300747 := by
  unfold tailWord_807074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7359101769529052527631069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19624271385410806740349517 7359101769529052527631069)
  ·
    refine ⟨2759663163573394697861651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7359101769529052527631069 2759663163573394697861651)
    ·
      refine ⟨4139494745360092046792477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759663163573394697861651 4139494745360092046792477)
      ·
        refine ⟨1552310529510034517547179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4139494745360092046792477 1552310529510034517547179)
        ·
          refine ⟨2328465794265051776320769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552310529510034517547179 2328465794265051776320769)
          ·
            refine ⟨1746349345698788832240577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328465794265051776320769 1746349345698788832240577)
            ·
              refine ⟨1309762009274091624180433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746349345698788832240577 1309762009274091624180433)
              ·
                refine ⟨982321506955568718135325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309762009274091624180433 982321506955568718135325)
                ·
                  refine ⟨368370565108338269300747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982321506955568718135325 368370565108338269300747)
                  ·
                    rfl

theorem cell20_807074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_807074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807074 prefixEnd_807074 := by exact prefixLift 807074
  have htrace : WordTrace (prefixWord ++ tailWord_807074) baseStart_807074 baseEnd_807074 := by
    simpa [prefixWord, tailWord_807074, baseEnd_807074] using wordTrace_append hprefix tailTrace_807074
  have hstable : (prefixWord ++ tailWord_807074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807074).length < 2 ^ (prefixWord ++ tailWord_807074).sum := by decide
  have hdescent : baseEnd_807074 < baseStart_807074 := by decide
  rcases family_descends (prefixWord ++ tailWord_807074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807105 : List Nat := [1, 2, 6, 1, 2, 1, 3, 4]
def baseStart_807105 : Nat := 118140960795 + 807105 * 2 ^ 59
def prefixEnd_807105 : Nat := 4983230072969 + 3 ^ 40 * 807105 * 2
def baseEnd_807105 : Nat := 122794904784346646422429

theorem tailTrace_807105 : CollatzResearch.WordTrace tailWord_807105 prefixEnd_807105 122794904784346646422429 := by
  unfold tailWord_807105
  simp only [CollatzResearch.WordTrace]
  refine ⟨29437537741003902404902769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19625025160669268269935179 29437537741003902404902769)
  ·
    refine ⟨22078153305752926803677077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29437537741003902404902769 22078153305752926803677077)
    ·
      refine ⟨1034913436207168443922363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22078153305752926803677077 1034913436207168443922363)
      ·
        refine ⟨1552370154310752665883545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034913436207168443922363 1552370154310752665883545)
        ·
          refine ⟨1164277615733064499412659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552370154310752665883545 1164277615733064499412659)
          ·
            refine ⟨1746416423599596749118989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164277615733064499412659 1746416423599596749118989)
            ·
              refine ⟨654906158849848780919621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1746416423599596749118989 654906158849848780919621)
              ·
                refine ⟨122794904784346646422429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654906158849848780919621 122794904784346646422429)
                ·
                  rfl

theorem cell20_807105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_807105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807105 prefixEnd_807105 := by exact prefixLift 807105
  have htrace : WordTrace (prefixWord ++ tailWord_807105) baseStart_807105 baseEnd_807105 := by
    simpa [prefixWord, tailWord_807105, baseEnd_807105] using wordTrace_append hprefix tailTrace_807105
  have hstable : (prefixWord ++ tailWord_807105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807105).length < 2 ^ (prefixWord ++ tailWord_807105).sum := by decide
  have hdescent : baseEnd_807105 < baseStart_807105 := by decide
  rcases family_descends (prefixWord ++ tailWord_807105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807126 : List Nat := [5, 2, 1, 2, 1, 2, 7]
def baseStart_807126 : Nat := 118140960795 + 807126 * 2 ^ 59
def prefixEnd_807126 : Nat := 4983230072969 + 3 ^ 40 * 807126 * 2
def baseEnd_807126 : Nat := 40932699925028577729689

theorem tailTrace_807126 : CollatzResearch.WordTrace tailWord_807126 prefixEnd_807126 40932699925028577729689 := by
  unfold tailWord_807126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839893979620488936963577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19625535782618548660944821 1839893979620488936963577)
  ·
    refine ⟨1379920484715366702722683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839893979620488936963577 1379920484715366702722683)
    ·
      refine ⟨2069880727073050054084025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379920484715366702722683 2069880727073050054084025)
      ·
        refine ⟨1552410545304787540563019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2069880727073050054084025 1552410545304787540563019)
        ·
          refine ⟨2328615817957181310844529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552410545304787540563019 2328615817957181310844529)
          ·
            refine ⟨1746461863467885983133397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328615817957181310844529 1746461863467885983133397)
            ·
              refine ⟨40932699925028577729689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1746461863467885983133397 40932699925028577729689)
              ·
                rfl

theorem cell20_807126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 7].length) (baseStart_807126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807126 prefixEnd_807126 := by exact prefixLift 807126
  have htrace : WordTrace (prefixWord ++ tailWord_807126) baseStart_807126 baseEnd_807126 := by
    simpa [prefixWord, tailWord_807126, baseEnd_807126] using wordTrace_append hprefix tailTrace_807126
  have hstable : (prefixWord ++ tailWord_807126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807126).length < 2 ^ (prefixWord ++ tailWord_807126).sum := by decide
  have hdescent : baseEnd_807126 < baseStart_807126 := by decide
  rcases family_descends (prefixWord ++ tailWord_807126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807133 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_807133 : Nat := 118140960795 + 807133 * 2 ^ 59
def prefixEnd_807133 : Nat := 4983230072969 + 3 ^ 40 * 807133 * 2
def baseEnd_807133 : Nat := 368397494315996286333839

theorem tailTrace_807133 : CollatzResearch.WordTrace tailWord_807133 prefixEnd_807133 368397494315996286333839 := by
  unfold tailWord_807133
  simp only [CollatzResearch.WordTrace]
  refine ⟨29438558984902463186922053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19625705989934975457948035 29438558984902463186922053)
  ·
    refine ⟨5519729809669211847547885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29438558984902463186922053 5519729809669211847547885)
    ·
      refine ⟨2069898678625954442830457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5519729809669211847547885 2069898678625954442830457)
      ·
        refine ⟨1552424008969465832122843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2069898678625954442830457 1552424008969465832122843)
        ·
          refine ⟨2328636013454198748184265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552424008969465832122843 2328636013454198748184265)
          ·
            refine ⟨1746477010090649061138199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328636013454198748184265 1746477010090649061138199)
            ·
              refine ⟨2619715515135973591707299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746477010090649061138199 2619715515135973591707299)
              ·
                refine ⟨3929573272703960387560949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619715515135973591707299 3929573272703960387560949)
                ·
                  refine ⟨368397494315996286333839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3929573272703960387560949 368397494315996286333839)
                  ·
                    rfl

theorem cell20_807133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_807133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807133 prefixEnd_807133 := by exact prefixLift 807133
  have htrace : WordTrace (prefixWord ++ tailWord_807133) baseStart_807133 baseEnd_807133 := by
    simpa [prefixWord, tailWord_807133, baseEnd_807133] using wordTrace_append hprefix tailTrace_807133
  have hstable : (prefixWord ++ tailWord_807133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807133).length < 2 ^ (prefixWord ++ tailWord_807133).sum := by decide
  have hdescent : baseEnd_807133 < baseStart_807133 := by decide
  rcases family_descends (prefixWord ++ tailWord_807133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807164 : List Nat := [2, 2, 2, 1, 4, 3, 2, 4]
def baseStart_807164 : Nat := 118140960795 + 807164 * 2 ^ 59
def prefixEnd_807164 : Nat := 4983230072969 + 3 ^ 40 * 807164 * 2
def baseEnd_807164 : Nat := 122803881186899318766793

theorem tailTrace_807164 : CollatzResearch.WordTrace tailWord_807164 prefixEnd_807164 122803881186899318766793 := by
  unfold tailWord_807164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719844823895077740650273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19626459765193436987533697 14719844823895077740650273)
  ·
    refine ⟨11039883617921308305487705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14719844823895077740650273 11039883617921308305487705)
    ·
      refine ⟨8279912713440981229115779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11039883617921308305487705 8279912713440981229115779)
      ·
        refine ⟨12419869070161471843673669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8279912713440981229115779 12419869070161471843673669)
        ·
          refine ⟨2328725450655275970688813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12419869070161471843673669 2328725450655275970688813)
          ·
            refine ⟨873272043995728489008305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2328725450655275970688813 873272043995728489008305)
            ·
              refine ⟨654954032996796366756229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873272043995728489008305 654954032996796366756229)
              ·
                refine ⟨122803881186899318766793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654954032996796366756229 122803881186899318766793)
                ·
                  rfl

theorem cell20_807164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_807164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807164 prefixEnd_807164 := by exact prefixLift 807164
  have htrace : WordTrace (prefixWord ++ tailWord_807164) baseStart_807164 baseEnd_807164 := by
    simpa [prefixWord, tailWord_807164, baseEnd_807164] using wordTrace_append hprefix tailTrace_807164
  have hstable : (prefixWord ++ tailWord_807164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807164).length < 2 ^ (prefixWord ++ tailWord_807164).sum := by decide
  have hdescent : baseEnd_807164 < baseStart_807164 := by decide
  rcases family_descends (prefixWord ++ tailWord_807164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807192 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_807192 : Nat := 118140960795 + 807192 * 2 ^ 59
def prefixEnd_807192 : Nat := 4983230072969 + 3 ^ 40 * 807192 * 2
def baseEnd_807192 : Nat := 368424423523654303366931

theorem tailTrace_807192 : CollatzResearch.WordTrace tailWord_807192 prefixEnd_807192 368424423523654303366931 := by
  unfold tailWord_807192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14720355445844358131659915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19627140594459144175546553 14720355445844358131659915)
  ·
    refine ⟨22080533168766537197489873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14720355445844358131659915 22080533168766537197489873)
    ·
      refine ⟨16560399876574902898117405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22080533168766537197489873 16560399876574902898117405)
      ·
        refine ⟨6210149953715588586794027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16560399876574902898117405 6210149953715588586794027)
        ·
          refine ⟨9315224930573382880191041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210149953715588586794027 9315224930573382880191041)
          ·
            refine ⟨6986418697930037160143281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9315224930573382880191041 6986418697930037160143281)
            ·
              refine ⟨5239814023447527870107461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6986418697930037160143281 5239814023447527870107461)
              ·
                refine ⟨982465129396411475645149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5239814023447527870107461 982465129396411475645149)
                ·
                  refine ⟨368424423523654303366931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982465129396411475645149 368424423523654303366931)
                  ·
                    rfl

theorem cell20_807192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_807192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807192 prefixEnd_807192 := by exact prefixLift 807192
  have htrace : WordTrace (prefixWord ++ tailWord_807192) baseStart_807192 baseEnd_807192 := by
    simpa [prefixWord, tailWord_807192, baseEnd_807192] using wordTrace_append hprefix tailTrace_807192
  have hstable : (prefixWord ++ tailWord_807192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807192).length < 2 ^ (prefixWord ++ tailWord_807192).sum := by decide
  have hdescent : baseEnd_807192 < baseStart_807192 := by decide
  rcases family_descends (prefixWord ++ tailWord_807192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807205 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 3]
def baseStart_807205 : Nat := 118140960795 + 807205 * 2 ^ 59
def prefixEnd_807205 : Nat := 4983230072969 + 3 ^ 40 * 807205 * 2
def baseEnd_807205 : Nat := 368430357077884035933545

theorem tailTrace_807205 : CollatzResearch.WordTrace tailWord_807205 prefixEnd_807205 368430357077884035933545 := by
  unfold tailWord_807205
  simp only [CollatzResearch.WordTrace]
  refine ⟨29441185040641619483543069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19627456693761079655695379 29441185040641619483543069)
  ·
    refine ⟨11040444390240607306328651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29441185040641619483543069 11040444390240607306328651)
    ·
      refine ⟨16560666585360910959492977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040444390240607306328651 16560666585360910959492977)
      ·
        refine ⟨12420499939020683219619733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16560666585360910959492977 12420499939020683219619733)
        ·
          refine ⟨582210934641594525919675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12420499939020683219619733 582210934641594525919675)
          ·
            refine ⟨873316401962391788879513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582210934641594525919675 873316401962391788879513)
            ·
              refine ⟨654987301471793841659635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873316401962391788879513 654987301471793841659635)
              ·
                refine ⟨982480952207690762489453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654987301471793841659635 982480952207690762489453)
                ·
                  refine ⟨368430357077884035933545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982480952207690762489453 368430357077884035933545)
                  ·
                    rfl

theorem cell20_807205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_807205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807205 prefixEnd_807205 := by exact prefixLift 807205
  have htrace : WordTrace (prefixWord ++ tailWord_807205) baseStart_807205 baseEnd_807205 := by
    simpa [prefixWord, tailWord_807205, baseEnd_807205] using wordTrace_append hprefix tailTrace_807205
  have hstable : (prefixWord ++ tailWord_807205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807205).length < 2 ^ (prefixWord ++ tailWord_807205).sum := by decide
  have hdescent : baseEnd_807205 < baseStart_807205 := by decide
  rcases family_descends (prefixWord ++ tailWord_807205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807268 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_807268 : Nat := 118140960795 + 807268 * 2 ^ 59
def prefixEnd_807268 : Nat := 4983230072969 + 3 ^ 40 * 807268 * 2
def baseEnd_807268 : Nat := 368459111994535816833287

theorem tailTrace_807268 : CollatzResearch.WordTrace tailWord_807268 prefixEnd_807268 368459111994535816833287 := by
  unfold tailWord_807268
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721741419706690621543229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19628988559608920828724305 14721741419706690621543229)
  ·
    refine ⟨5520653032390008983078711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14721741419706690621543229 5520653032390008983078711)
    ·
      refine ⟨8280979548585013474618067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5520653032390008983078711 8280979548585013474618067)
      ·
        refine ⟨12421469322877520211927101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8280979548585013474618067 12421469322877520211927101)
        ·
          refine ⟨4658050996079070079472663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12421469322877520211927101 4658050996079070079472663)
          ·
            refine ⟨6987076494118605119208995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658050996079070079472663 6987076494118605119208995)
            ·
              refine ⟨10480614741177907678813493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987076494118605119208995 10480614741177907678813493)
              ·
                refine ⟨982557631985428844888765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10480614741177907678813493 982557631985428844888765)
                ·
                  refine ⟨368459111994535816833287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982557631985428844888765 368459111994535816833287)
                  ·
                    rfl

theorem cell20_807268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_807268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807268 prefixEnd_807268 := by exact prefixLift 807268
  have htrace : WordTrace (prefixWord ++ tailWord_807268) baseStart_807268 baseEnd_807268 := by
    simpa [prefixWord, tailWord_807268, baseEnd_807268] using wordTrace_append hprefix tailTrace_807268
  have hstable : (prefixWord ++ tailWord_807268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807268).length < 2 ^ (prefixWord ++ tailWord_807268).sum := by decide
  have hdescent : baseEnd_807268 < baseStart_807268 := by decide
  rcases family_descends (prefixWord ++ tailWord_807268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807289 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_807289 : Nat := 118140960795 + 807289 * 2 ^ 59
def prefixEnd_807289 : Nat := 4983230072969 + 3 ^ 40 * 807289 * 2
def baseEnd_807289 : Nat := 368468696966753077133201

theorem tailTrace_807289 : CollatzResearch.WordTrace tailWord_807289 prefixEnd_807289 368468696966753077133201 := by
  unfold tailWord_807289
  simp only [CollatzResearch.WordTrace]
  refine ⟨29444248772337301829600921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19629499181558201219733947 29444248772337301829600921)
  ·
    refine ⟨22083186579252976372200691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29444248772337301829600921 22083186579252976372200691)
    ·
      refine ⟨33124779868879464558301037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22083186579252976372200691 33124779868879464558301037)
      ·
        refine ⟨12421792450829799209362889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33124779868879464558301037 12421792450829799209362889)
        ·
          refine ⟨9316344338122349407022167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12421792450829799209362889 9316344338122349407022167)
          ·
            refine ⟨13974516507183524110533251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9316344338122349407022167 13974516507183524110533251)
            ·
              refine ⟨20961774760775286165799877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13974516507183524110533251 20961774760775286165799877)
              ·
                refine ⟨3930332767645366156087477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20961774760775286165799877 3930332767645366156087477)
                ·
                  refine ⟨368468696966753077133201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3930332767645366156087477 368468696966753077133201)
                  ·
                    rfl

theorem cell20_807289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_807289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807289 prefixEnd_807289 := by exact prefixLift 807289
  have htrace : WordTrace (prefixWord ++ tailWord_807289) baseStart_807289 baseEnd_807289 := by
    simpa [prefixWord, tailWord_807289, baseEnd_807289] using wordTrace_append hprefix tailTrace_807289
  have hstable : (prefixWord ++ tailWord_807289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807289).length < 2 ^ (prefixWord ++ tailWord_807289).sum := by decide
  have hdescent : baseEnd_807289 < baseStart_807289 := by decide
  rcases family_descends (prefixWord ++ tailWord_807289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807298 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 3]
def baseStart_807298 : Nat := 118140960795 + 807298 * 2 ^ 59
def prefixEnd_807298 : Nat := 4983230072969 + 3 ^ 40 * 807298 * 2
def baseEnd_807298 : Nat := 368472804811989045833165

theorem tailTrace_807298 : CollatzResearch.WordTrace tailWord_807298 prefixEnd_807298 368472804811989045833165 := by
  unfold tailWord_807298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361144257326174091669637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19629718019536464244452365 7361144257326174091669637)
  ·
    refine ⟨1380214548248657642188057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7361144257326174091669637 1380214548248657642188057)
    ·
      refine ⟨1035160911186493231641043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380214548248657642188057 1035160911186493231641043)
      ·
        refine ⟨1552741366779739847461565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035160911186493231641043 1552741366779739847461565)
        ·
          refine ⟨582278012542402442798087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1552741366779739847461565 582278012542402442798087)
          ·
            refine ⟨873417018813603664197131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582278012542402442798087 873417018813603664197131)
            ·
              refine ⟨1310125528220405496295697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873417018813603664197131 1310125528220405496295697)
              ·
                refine ⟨982594146165304122221773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310125528220405496295697 982594146165304122221773)
                ·
                  refine ⟨368472804811989045833165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982594146165304122221773 368472804811989045833165)
                  ·
                    rfl

theorem cell20_807298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_807298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807298 prefixEnd_807298 := by exact prefixLift 807298
  have htrace : WordTrace (prefixWord ++ tailWord_807298) baseStart_807298 baseEnd_807298 := by
    simpa [prefixWord, tailWord_807298, baseEnd_807298] using wordTrace_append hprefix tailTrace_807298
  have hstable : (prefixWord ++ tailWord_807298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807298).length < 2 ^ (prefixWord ++ tailWord_807298).sum := by decide
  have hdescent : baseEnd_807298 < baseStart_807298 := by decide
  rcases family_descends (prefixWord ++ tailWord_807298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807358 : List Nat := [4, 2, 1, 1, 1, 1, 10]
def baseStart_807358 : Nat := 118140960795 + 807358 * 2 ^ 59
def prefixEnd_807358 : Nat := 4983230072969 + 3 ^ 40 * 807358 * 2
def baseEnd_807358 : Nat := 40944465605210611536991

theorem tailTrace_807358 : CollatzResearch.WordTrace tailWord_807358 prefixEnd_807358 40944465605210611536991 := by
  unfold tailWord_807358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680845676135915826732841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19631176939391551075908485 3680845676135915826732841)
  ·
    refine ⟨2760634257101936870049631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3680845676135915826732841 2760634257101936870049631)
    ·
      refine ⟨4140951385652905305074447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760634257101936870049631 4140951385652905305074447)
      ·
        refine ⟨6211427078479357957611671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140951385652905305074447 6211427078479357957611671)
        ·
          refine ⟨9317140617719036936417507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211427078479357957611671 9317140617719036936417507)
          ·
            refine ⟨13975710926578555404626261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9317140617719036936417507 13975710926578555404626261)
            ·
              refine ⟨40944465605210611536991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13975710926578555404626261 40944465605210611536991)
              ·
                rfl

theorem cell20_807358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 10].length) (baseStart_807358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807358 prefixEnd_807358 := by exact prefixLift 807358
  have htrace : WordTrace (prefixWord ++ tailWord_807358) baseStart_807358 baseEnd_807358 := by
    simpa [prefixWord, tailWord_807358, baseEnd_807358] using wordTrace_append hprefix tailTrace_807358
  have hstable : (prefixWord ++ tailWord_807358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807358).length < 2 ^ (prefixWord ++ tailWord_807358).sum := by decide
  have hdescent : baseEnd_807358 < baseStart_807358 := by decide
  rcases family_descends (prefixWord ++ tailWord_807358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807364 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 4]
def baseStart_807364 : Nat := 118140960795 + 807364 * 2 ^ 59
def prefixEnd_807364 : Nat := 4983230072969 + 3 ^ 40 * 807364 * 2
def baseEnd_807364 : Nat := 368502929010386149632895

theorem tailTrace_807364 : CollatzResearch.WordTrace tailWord_807364 prefixEnd_807364 368502929010386149632895 := by
  unfold tailWord_807364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723492123532794819290573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19631322831377059759054097 14723492123532794819290573)
  ·
    refine ⟨5521309546324798057233965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14723492123532794819290573 5521309546324798057233965)
    ·
      refine ⟨2070491079871799271462737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5521309546324798057233965 2070491079871799271462737)
      ·
        refine ⟨1552868309903849453597053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2070491079871799271462737 1552868309903849453597053)
        ·
          refine ⟨582325616213943545098895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1552868309903849453597053 582325616213943545098895)
          ·
            refine ⟨873488424320915317648343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582325616213943545098895 873488424320915317648343)
            ·
              refine ⟨1310232636481372976472515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873488424320915317648343 1310232636481372976472515)
              ·
                refine ⟨1965348954722059464708773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310232636481372976472515 1965348954722059464708773)
                ·
                  refine ⟨368502929010386149632895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965348954722059464708773 368502929010386149632895)
                  ·
                    rfl

theorem cell20_807364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_807364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807364 prefixEnd_807364 := by exact prefixLift 807364
  have htrace : WordTrace (prefixWord ++ tailWord_807364) baseStart_807364 baseEnd_807364 := by
    simpa [prefixWord, tailWord_807364, baseEnd_807364] using wordTrace_append hprefix tailTrace_807364
  have hstable : (prefixWord ++ tailWord_807364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807364).length < 2 ^ (prefixWord ++ tailWord_807364).sum := by decide
  have hdescent : baseEnd_807364 < baseStart_807364 := by decide
  rcases family_descends (prefixWord ++ tailWord_807364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807368 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_807368 : Nat := 118140960795 + 807368 * 2 ^ 59
def prefixEnd_807368 : Nat := 4983230072969 + 3 ^ 40 * 807368 * 2
def baseEnd_807368 : Nat := 368504754719379913499545

theorem tailTrace_807368 : CollatzResearch.WordTrace tailWord_807368 prefixEnd_807368 368504754719379913499545 := by
  unfold tailWord_807368
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723565069525549160863379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19631420092700732214484505 14723565069525549160863379)
  ·
    refine ⟨22085347604288323741295069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14723565069525549160863379 22085347604288323741295069)
    ·
      refine ⟨8282005351608121402985651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22085347604288323741295069 8282005351608121402985651)
      ·
        refine ⟨12423008027412182104478477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282005351608121402985651 12423008027412182104478477)
        ·
          refine ⟨4658628010279568289179429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12423008027412182104478477 4658628010279568289179429)
          ·
            refine ⟨873492751927419054221143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4658628010279568289179429 873492751927419054221143)
            ·
              refine ⟨1310239127891128581331715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873492751927419054221143 1310239127891128581331715)
              ·
                refine ⟨1965358691836692871997573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310239127891128581331715 1965358691836692871997573)
                ·
                  refine ⟨368504754719379913499545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965358691836692871997573 368504754719379913499545)
                  ·
                    rfl

theorem cell20_807368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_807368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807368 prefixEnd_807368 := by exact prefixLift 807368
  have htrace : WordTrace (prefixWord ++ tailWord_807368) baseStart_807368 baseEnd_807368 := by
    simpa [prefixWord, tailWord_807368, baseEnd_807368] using wordTrace_append hprefix tailTrace_807368
  have hstable : (prefixWord ++ tailWord_807368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807368).length < 2 ^ (prefixWord ++ tailWord_807368).sum := by decide
  have hdescent : baseEnd_807368 < baseStart_807368 := by decide
  rcases family_descends (prefixWord ++ tailWord_807368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807378 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_807378 : Nat := 118140960795 + 807378 * 2 ^ 59
def prefixEnd_807378 : Nat := 4983230072969 + 3 ^ 40 * 807378 * 2
def baseEnd_807378 : Nat := 368509318991864323166171

theorem tailTrace_807378 : CollatzResearch.WordTrace tailWord_807378 prefixEnd_807378 368509318991864323166171 := by
  unfold tailWord_807378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361873717253717507397697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19631663246009913353060525 7361873717253717507397697)
  ·
    refine ⟨5521405287940288130548273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7361873717253717507397697 5521405287940288130548273)
    ·
      refine ⟨4141053965955216097911205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5521405287940288130548273 4141053965955216097911205)
      ·
        refine ⟨776447618616603018358351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4141053965955216097911205 776447618616603018358351)
        ·
          refine ⟨1164671427924904527537527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776447618616603018358351 1164671427924904527537527)
          ·
            refine ⟨1747007141887356791306291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164671427924904527537527 1747007141887356791306291)
            ·
              refine ⟨2620510712831035186959437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747007141887356791306291 2620510712831035186959437)
              ·
                refine ⟨982691517311638195109789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2620510712831035186959437 982691517311638195109789)
                ·
                  refine ⟨368509318991864323166171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982691517311638195109789 368509318991864323166171)
                  ·
                    rfl

theorem cell20_807378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_807378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807378 prefixEnd_807378 := by exact prefixLift 807378
  have htrace : WordTrace (prefixWord ++ tailWord_807378) baseStart_807378 baseEnd_807378 := by
    simpa [prefixWord, tailWord_807378, baseEnd_807378] using wordTrace_append hprefix tailTrace_807378
  have hstable : (prefixWord ++ tailWord_807378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807378).length < 2 ^ (prefixWord ++ tailWord_807378).sum := by decide
  have hdescent : baseEnd_807378 < baseStart_807378 := by decide
  rcases family_descends (prefixWord ++ tailWord_807378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807389 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_807389 : Nat := 118140960795 + 807389 * 2 ^ 59
def prefixEnd_807389 : Nat := 4983230072969 + 3 ^ 40 * 807389 * 2
def baseEnd_807389 : Nat := 368514339691597173799459

theorem tailTrace_807389 : CollatzResearch.WordTrace tailWord_807389 prefixEnd_807389 368514339691597173799459 := by
  unfold tailWord_807389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29447896071975018908241221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19631930714650012605494147 29447896071975018908241221)
  ·
    refine ⟨5521480513495316045295229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29447896071975018908241221 5521480513495316045295229)
    ·
      refine ⟨2070555192560743516985711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5521480513495316045295229 2070555192560743516985711)
      ·
        refine ⟨3105832788841115275478567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070555192560743516985711 3105832788841115275478567)
        ·
          refine ⟨4658749183261672913217851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105832788841115275478567 4658749183261672913217851)
          ·
            refine ⟨6988123774892509369826777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658749183261672913217851 6988123774892509369826777)
            ·
              refine ⟨5241092831169382027370083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988123774892509369826777 5241092831169382027370083)
              ·
                refine ⟨7861639246754073041055125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241092831169382027370083 7861639246754073041055125)
                ·
                  refine ⟨368514339691597173799459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7861639246754073041055125 368514339691597173799459)
                  ·
                    rfl

theorem cell20_807389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_807389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807389 prefixEnd_807389 := by exact prefixLift 807389
  have htrace : WordTrace (prefixWord ++ tailWord_807389) baseStart_807389 baseEnd_807389 := by
    simpa [prefixWord, tailWord_807389, baseEnd_807389] using wordTrace_append hprefix tailTrace_807389
  have hstable : (prefixWord ++ tailWord_807389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807389).length < 2 ^ (prefixWord ++ tailWord_807389).sum := by decide
  have hdescent : baseEnd_807389 < baseStart_807389 := by decide
  rcases family_descends (prefixWord ++ tailWord_807389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807413 : List Nat := [1, 3, 5, 1, 2, 8]
def baseStart_807413 : Nat := 118140960795 + 807413 * 2 ^ 59
def prefixEnd_807413 : Nat := 4983230072969 + 3 ^ 40 * 807413 * 2
def baseEnd_807413 : Nat := 13649084960946657666643

theorem tailTrace_807413 : CollatzResearch.WordTrace tailWord_807413 prefixEnd_807413 13649084960946657666643 := by
  unfold tailWord_807413
  simp only [CollatzResearch.WordTrace]
  refine ⟨29448771423888071007114893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19632514282592047338076595 29448771423888071007114893)
  ·
    refine ⟨11043289283958026627668085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29448771423888071007114893 11043289283958026627668085)
    ·
      refine ⟨1035308370371064996343883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11043289283958026627668085 1035308370371064996343883)
      ·
        refine ⟨1552962555556597494515825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035308370371064996343883 1552962555556597494515825)
        ·
          refine ⟨1164721916667448120886869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552962555556597494515825 1164721916667448120886869)
          ·
            refine ⟨13649084960946657666643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1164721916667448120886869 13649084960946657666643)
            ·
              rfl

theorem cell20_807413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 8].length) (baseStart_807413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807413 prefixEnd_807413 := by exact prefixLift 807413
  have htrace : WordTrace (prefixWord ++ tailWord_807413) baseStart_807413 baseEnd_807413 := by
    simpa [prefixWord, tailWord_807413, baseEnd_807413] using wordTrace_append hprefix tailTrace_807413
  have hstable : (prefixWord ++ tailWord_807413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807413).length < 2 ^ (prefixWord ++ tailWord_807413).sum := by decide
  have hdescent : baseEnd_807413 < baseStart_807413 := by decide
  rcases family_descends (prefixWord ++ tailWord_807413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807444 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_807444 : Nat := 118140960795 + 807444 * 2 ^ 59
def prefixEnd_807444 : Nat := 4983230072969 + 3 ^ 40 * 807444 * 2
def baseEnd_807444 : Nat := 368539443190261426965901

theorem tailTrace_807444 : CollatzResearch.WordTrace tailWord_807444 prefixEnd_807444 368539443190261426965901 := by
  unfold tailWord_807444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14724951043387881650746693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19633268057850508867662257 14724951043387881650746693)
  ·
    refine ⟨2760928320635227809515005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14724951043387881650746693 2760928320635227809515005)
    ·
      refine ⟨1035348120238210428568127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2760928320635227809515005 1035348120238210428568127)
      ·
        refine ⟨1553022180357315642852191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035348120238210428568127 1553022180357315642852191)
        ·
          refine ⟨2329533270535973464278287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553022180357315642852191 2329533270535973464278287)
          ·
            refine ⟨3494299905803960196417431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329533270535973464278287 3494299905803960196417431)
            ·
              refine ⟨5241449858705940294626147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494299905803960196417431 5241449858705940294626147)
              ·
                refine ⟨7862174788058910441939221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241449858705940294626147 7862174788058910441939221)
                ·
                  refine ⟨368539443190261426965901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7862174788058910441939221 368539443190261426965901)
                  ·
                    rfl

theorem cell20_807444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_807444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807444 prefixEnd_807444 := by exact prefixLift 807444
  have htrace : WordTrace (prefixWord ++ tailWord_807444) baseStart_807444 baseEnd_807444 := by
    simpa [prefixWord, tailWord_807444, baseEnd_807444] using wordTrace_append hprefix tailTrace_807444
  have hstable : (prefixWord ++ tailWord_807444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807444).length < 2 ^ (prefixWord ++ tailWord_807444).sum := by decide
  have hdescent : baseEnd_807444 < baseStart_807444 := by decide
  rcases family_descends (prefixWord ++ tailWord_807444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807479 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_807479 : Nat := 118140960795 + 807479 * 2 ^ 59
def prefixEnd_807479 : Nat := 4983230072969 + 3 ^ 40 * 807479 * 2
def baseEnd_807479 : Nat := 368555418143956860799091

theorem tailTrace_807479 : CollatzResearch.WordTrace tailWord_807479 prefixEnd_807479 368555418143956860799091 := by
  unfold tailWord_807479
  simp only [CollatzResearch.WordTrace]
  refine ⟨29451178641648964279017491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19634119094432642852678327 29451178641648964279017491)
  ·
    refine ⟨44176767962473446418526237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29451178641648964279017491 44176767962473446418526237)
    ·
      refine ⟨16566287985927542406947339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44176767962473446418526237 16566287985927542406947339)
      ·
        refine ⟨24849431978891313610421009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16566287985927542406947339 24849431978891313610421009)
        ·
          refine ⟨18637073984168485207815757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24849431978891313610421009 18637073984168485207815757)
          ·
            refine ⟨6988902744063181952930909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18637073984168485207815757 6988902744063181952930909)
            ·
              refine ⟨2620838529023693232349091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6988902744063181952930909 2620838529023693232349091)
              ·
                refine ⟨3931257793535539848523637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620838529023693232349091 3931257793535539848523637)
                ·
                  refine ⟨368555418143956860799091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3931257793535539848523637 368555418143956860799091)
                  ·
                    rfl

theorem cell20_807479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_807479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807479 prefixEnd_807479 := by exact prefixLift 807479
  have htrace : WordTrace (prefixWord ++ tailWord_807479) baseStart_807479 baseEnd_807479 := by
    simpa [prefixWord, tailWord_807479, baseEnd_807479] using wordTrace_append hprefix tailTrace_807479
  have hstable : (prefixWord ++ tailWord_807479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807479).length < 2 ^ (prefixWord ++ tailWord_807479).sum := by decide
  have hdescent : baseEnd_807479 < baseStart_807479 := by decide
  rcases family_descends (prefixWord ++ tailWord_807479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807482 : List Nat := [3, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_807482 : Nat := 118140960795 + 807482 * 2 ^ 59
def prefixEnd_807482 : Nat := 4983230072969 + 3 ^ 40 * 807482 * 2
def baseEnd_807482 : Nat := 368556787425702183699079

theorem tailTrace_807482 : CollatzResearch.WordTrace tailWord_807482 prefixEnd_807482 368556787425702183699079 := by
  unfold tailWord_807482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7362822015159523947844175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19634192040425397194251133 7362822015159523947844175)
  ·
    refine ⟨11044233022739285921766263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7362822015159523947844175 11044233022739285921766263)
    ·
      refine ⟨16566349534108928882649395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11044233022739285921766263 16566349534108928882649395)
      ·
        refine ⟨24849524301163393323974093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16566349534108928882649395 24849524301163393323974093)
        ·
          refine ⟨9318571612936272496490285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24849524301163393323974093 9318571612936272496490285)
          ·
            refine ⟨3494464354851102186183857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9318571612936272496490285 3494464354851102186183857)
            ·
              refine ⟨2620848266138326639637893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494464354851102186183857 2620848266138326639637893)
              ·
                refine ⟨491409049900936244932105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2620848266138326639637893 491409049900936244932105)
                ·
                  refine ⟨368556787425702183699079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491409049900936244932105 368556787425702183699079)
                  ·
                    rfl

theorem cell20_807482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_807482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807482 prefixEnd_807482 := by exact prefixLift 807482
  have htrace : WordTrace (prefixWord ++ tailWord_807482) baseStart_807482 baseEnd_807482 := by
    simpa [prefixWord, tailWord_807482, baseEnd_807482] using wordTrace_append hprefix tailTrace_807482
  have hstable : (prefixWord ++ tailWord_807482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807482).length < 2 ^ (prefixWord ++ tailWord_807482).sum := by decide
  have hdescent : baseEnd_807482 < baseStart_807482 := by decide
  rcases family_descends (prefixWord ++ tailWord_807482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807516 : List Nat := [2, 2, 4, 1, 3, 2, 1, 3, 2]
def baseStart_807516 : Nat := 118140960795 + 807516 * 2 ^ 59
def prefixEnd_807516 : Nat := 4983230072969 + 3 ^ 40 * 807516 * 2
def baseEnd_807516 : Nat := 368572305952149176565607

theorem tailTrace_807516 : CollatzResearch.WordTrace tailWord_807516 prefixEnd_807516 368572305952149176565607 := by
  unfold tailWord_807516
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726264071257459799057201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19635018761676613065409601 14726264071257459799057201)
  ·
    refine ⟨11044698053443094849292901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14726264071257459799057201 11044698053443094849292901)
    ·
      refine ⟨2070880885020580284242419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11044698053443094849292901 2070880885020580284242419)
      ·
        refine ⟨3106321327530870426363629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070880885020580284242419 3106321327530870426363629)
        ·
          refine ⟨1164870497824076409886361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3106321327530870426363629 1164870497824076409886361)
          ·
            refine ⟨873652873368057307414771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164870497824076409886361 873652873368057307414771)
            ·
              refine ⟨1310479310052085961122157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873652873368057307414771 1310479310052085961122157)
              ·
                refine ⟨491429741269532235420809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310479310052085961122157 491429741269532235420809)
                ·
                  refine ⟨368572305952149176565607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491429741269532235420809 368572305952149176565607)
                  ·
                    rfl

theorem cell20_807516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_807516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807516 prefixEnd_807516 := by exact prefixLift 807516
  have htrace : WordTrace (prefixWord ++ tailWord_807516) baseStart_807516 baseEnd_807516 := by
    simpa [prefixWord, tailWord_807516, baseEnd_807516] using wordTrace_append hprefix tailTrace_807516
  have hstable : (prefixWord ++ tailWord_807516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807516).length < 2 ^ (prefixWord ++ tailWord_807516).sum := by decide
  have hdescent : baseEnd_807516 < baseStart_807516 := by decide
  rcases family_descends (prefixWord ++ tailWord_807516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807520 : List Nat := [2, 1, 1, 3, 2, 1, 5, 3, 2]
def baseStart_807520 : Nat := 118140960795 + 807520 * 2 ^ 59
def prefixEnd_807520 : Nat := 4983230072969 + 3 ^ 40 * 807520 * 2
def baseEnd_807520 : Nat := 368574131661142940432257

theorem tailTrace_807520 : CollatzResearch.WordTrace tailWord_807520 prefixEnd_807520 368574131661142940432257 := by
  unfold tailWord_807520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726337017250214140630007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19635116023000285520840009 14726337017250214140630007)
  ·
    refine ⟨22089505525875321210945011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14726337017250214140630007 22089505525875321210945011)
    ·
      refine ⟨33134258288812981816417517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22089505525875321210945011 33134258288812981816417517)
      ·
        refine ⟨12425346858304868181156569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33134258288812981816417517 12425346858304868181156569)
        ·
          refine ⟨9319010143728651135867427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12425346858304868181156569 9319010143728651135867427)
          ·
            refine ⟨13978515215592976703801141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9319010143728651135867427 13978515215592976703801141)
            ·
              refine ⟨1310485801461841565981357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13978515215592976703801141 1310485801461841565981357)
              ·
                refine ⟨491432175548190587243009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310485801461841565981357 491432175548190587243009)
                ·
                  refine ⟨368574131661142940432257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491432175548190587243009 368574131661142940432257)
                  ·
                    rfl

theorem cell20_807520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_807520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807520 prefixEnd_807520 := by exact prefixLift 807520
  have htrace : WordTrace (prefixWord ++ tailWord_807520) baseStart_807520 baseEnd_807520 := by
    simpa [prefixWord, tailWord_807520, baseEnd_807520] using wordTrace_append hprefix tailTrace_807520
  have hstable : (prefixWord ++ tailWord_807520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807520).length < 2 ^ (prefixWord ++ tailWord_807520).sum := by decide
  have hdescent : baseEnd_807520 < baseStart_807520 := by decide
  rcases family_descends (prefixWord ++ tailWord_807520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807534 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_807534 : Nat := 118140960795 + 807534 * 2 ^ 59
def prefixEnd_807534 : Nat := 4983230072969 + 3 ^ 40 * 807534 * 2
def baseEnd_807534 : Nat := 368580521642621113965533

theorem tailTrace_807534 : CollatzResearch.WordTrace tailWord_807534 prefixEnd_807534 368580521642621113965533 := by
  unfold tailWord_807534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681648082056213584033707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19635456437633139114846437 3681648082056213584033707)
  ·
    refine ⟨5522472123084320376050561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3681648082056213584033707 5522472123084320376050561)
    ·
      refine ⟨4141854092313240282037921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5522472123084320376050561 4141854092313240282037921)
      ·
        refine ⟨3106390569234930211528441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4141854092313240282037921 3106390569234930211528441)
        ·
          refine ⟨2329792926926197658646331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3106390569234930211528441 2329792926926197658646331)
          ·
            refine ⟨3494689390389296487969497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329792926926197658646331 3494689390389296487969497)
            ·
              refine ⟨2621017042791972365977123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494689390389296487969497 2621017042791972365977123)
              ·
                refine ⟨3931525564187958548965685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621017042791972365977123 3931525564187958548965685)
                ·
                  refine ⟨368580521642621113965533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3931525564187958548965685 368580521642621113965533)
                  ·
                    rfl

theorem cell20_807534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_807534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807534 prefixEnd_807534 := by exact prefixLift 807534
  have htrace : WordTrace (prefixWord ++ tailWord_807534) baseStart_807534 baseEnd_807534 := by
    simpa [prefixWord, tailWord_807534, baseEnd_807534] using wordTrace_append hprefix tailTrace_807534
  have hstable : (prefixWord ++ tailWord_807534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807534).length < 2 ^ (prefixWord ++ tailWord_807534).sum := by decide
  have hdescent : baseEnd_807534 < baseStart_807534 := by decide
  rcases family_descends (prefixWord ++ tailWord_807534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807593 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 3]
def baseStart_807593 : Nat := 118140960795 + 807593 * 2 ^ 59
def prefixEnd_807593 : Nat := 4983230072969 + 3 ^ 40 * 807593 * 2
def baseEnd_807593 : Nat := 368607450850279130998625

theorem tailTrace_807593 : CollatzResearch.WordTrace tailWord_807593 prefixEnd_807593 368607450850279130998625 := by
  unfold tailWord_807593
  simp only [CollatzResearch.WordTrace]
  refine ⟨29455336563235961748667433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19636891042157307832444955 29455336563235961748667433)
  ·
    refine ⟨22091502422426971311500575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29455336563235961748667433 22091502422426971311500575)
    ·
      refine ⟨33137253633640456967250863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22091502422426971311500575 33137253633640456967250863)
      ·
        refine ⟨49705880450460685450876295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33137253633640456967250863 49705880450460685450876295)
        ·
          refine ⟨74558820675691028176314443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49705880450460685450876295 74558820675691028176314443)
          ·
            refine ⟨111838231013536542264471665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74558820675691028176314443 111838231013536542264471665)
            ·
              refine ⟨83878673260152406698353749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111838231013536542264471665 83878673260152406698353749)
              ·
                refine ⟨982953202267411015996333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 83878673260152406698353749 982953202267411015996333)
                ·
                  refine ⟨368607450850279130998625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982953202267411015996333 368607450850279130998625)
                  ·
                    rfl

theorem cell20_807593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_807593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807593 prefixEnd_807593 := by exact prefixLift 807593
  have htrace : WordTrace (prefixWord ++ tailWord_807593) baseStart_807593 baseEnd_807593 := by
    simpa [prefixWord, tailWord_807593, baseEnd_807593] using wordTrace_append hprefix tailTrace_807593
  have hstable : (prefixWord ++ tailWord_807593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807593).length < 2 ^ (prefixWord ++ tailWord_807593).sum := by decide
  have hdescent : baseEnd_807593 < baseStart_807593 := by decide
  rcases family_descends (prefixWord ++ tailWord_807593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807600 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_807600 : Nat := 118140960795 + 807600 * 2 ^ 59
def prefixEnd_807600 : Nat := 4983230072969 + 3 ^ 40 * 807600 * 2
def baseEnd_807600 : Nat := 368610645841018217765263

theorem tailTrace_807600 : CollatzResearch.WordTrace tailWord_807600 prefixEnd_807600 368610645841018217765263 := by
  unfold tailWord_807600
  simp only [CollatzResearch.WordTrace]
  refine ⟨14727795937105300972086127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19637061249473734629448169 14727795937105300972086127)
  ·
    refine ⟨22091693905657951458129191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14727795937105300972086127 22091693905657951458129191)
    ·
      refine ⟨33137540858486927187193787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22091693905657951458129191 33137540858486927187193787)
      ·
        refine ⟨49706311287730390780790681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33137540858486927187193787 49706311287730390780790681)
        ·
          refine ⟨37279733465797793085593011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49706311287730390780790681 37279733465797793085593011)
          ·
            refine ⟨55919600198696689628389517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37279733465797793085593011 55919600198696689628389517)
            ·
              refine ⟨20969850074511258610646069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55919600198696689628389517 20969850074511258610646069)
              ·
                refine ⟨1965923444485430494748069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20969850074511258610646069 1965923444485430494748069)
                ·
                  refine ⟨368610645841018217765263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965923444485430494748069 368610645841018217765263)
                  ·
                    rfl

theorem cell20_807600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_807600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807600 prefixEnd_807600 := by exact prefixLift 807600
  have htrace : WordTrace (prefixWord ++ tailWord_807600) baseStart_807600 baseEnd_807600 := by
    simpa [prefixWord, tailWord_807600, baseEnd_807600] using wordTrace_append hprefix tailTrace_807600
  have hstable : (prefixWord ++ tailWord_807600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807600).length < 2 ^ (prefixWord ++ tailWord_807600).sum := by decide
  have hdescent : baseEnd_807600 < baseStart_807600 := by decide
  rcases family_descends (prefixWord ++ tailWord_807600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807644 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_807644 : Nat := 118140960795 + 807644 * 2 ^ 59
def prefixEnd_807644 : Nat := 4983230072969 + 3 ^ 40 * 807644 * 2
def baseEnd_807644 : Nat := 368630728639949620298417

theorem tailTrace_807644 : CollatzResearch.WordTrace tailWord_807644 prefixEnd_807644 368630728639949620298417 := by
  unfold tailWord_807644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14728598343025598729386993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19638131124034131639182657 14728598343025598729386993)
  ·
    refine ⟨11046448757269199047040245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14728598343025598729386993 11046448757269199047040245)
    ·
      refine ⟨1035604570993987410660023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11046448757269199047040245 1035604570993987410660023)
      ·
        refine ⟨1553406856490981115990035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035604570993987410660023 1553406856490981115990035)
        ·
          refine ⟨2330110284736471673985053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553406856490981115990035 2330110284736471673985053)
          ·
            refine ⟨873791356776176877744395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2330110284736471673985053 873791356776176877744395)
            ·
              refine ⟨1310687035164265316616593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873791356776176877744395 1310687035164265316616593)
              ·
                refine ⟨983015276373198987462445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310687035164265316616593 983015276373198987462445)
                ·
                  refine ⟨368630728639949620298417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983015276373198987462445 368630728639949620298417)
                  ·
                    rfl

theorem cell20_807644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_807644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807644 prefixEnd_807644 := by exact prefixLift 807644
  have htrace : WordTrace (prefixWord ++ tailWord_807644) baseStart_807644 baseEnd_807644 := by
    simpa [prefixWord, tailWord_807644, baseEnd_807644] using wordTrace_append hprefix tailTrace_807644
  have hstable : (prefixWord ++ tailWord_807644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807644).length < 2 ^ (prefixWord ++ tailWord_807644).sum := by decide
  have hdescent : baseEnd_807644 < baseStart_807644 := by decide
  rcases family_descends (prefixWord ++ tailWord_807644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807762 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_807762 : Nat := 118140960795 + 807762 * 2 ^ 59
def prefixEnd_807762 : Nat := 4983230072969 + 3 ^ 40 * 807762 * 2
def baseEnd_807762 : Nat := 368684587055265654364601

theorem tailTrace_807762 : CollatzResearch.WordTrace tailWord_807762 prefixEnd_807762 368684587055265654364601 := by
  unfold tailWord_807762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7365375124905925902892385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19641000333082469074379693 7365375124905925902892385)
  ·
    refine ⟨5524031343679444427169289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7365375124905925902892385 5524031343679444427169289)
    ·
      refine ⟨4143023507759583320376967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5524031343679444427169289 4143023507759583320376967)
      ·
        refine ⟨6214535261639374980565451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4143023507759583320376967 6214535261639374980565451)
        ·
          refine ⟨9321802892459062470848177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214535261639374980565451 9321802892459062470848177)
          ·
            refine ⟨6991352169344296853136133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9321802892459062470848177 6991352169344296853136133)
            ·
              refine ⟨1310878531752055659963025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6991352169344296853136133 1310878531752055659963025)
              ·
                refine ⟨983158898814041744972269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310878531752055659963025 983158898814041744972269)
                ·
                  refine ⟨368684587055265654364601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983158898814041744972269 368684587055265654364601)
                  ·
                    rfl

theorem cell20_807762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_807762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807762 prefixEnd_807762 := by exact prefixLift 807762
  have htrace : WordTrace (prefixWord ++ tailWord_807762) baseStart_807762 baseEnd_807762 := by
    simpa [prefixWord, tailWord_807762, baseEnd_807762] using wordTrace_append hprefix tailTrace_807762
  have hstable : (prefixWord ++ tailWord_807762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807762).length < 2 ^ (prefixWord ++ tailWord_807762).sum := by decide
  have hdescent : baseEnd_807762 < baseStart_807762 := by decide
  rcases family_descends (prefixWord ++ tailWord_807762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807807 : List Nat := [1, 1, 2, 2, 1, 1, 5, 5, 2]
def baseStart_807807 : Nat := 118140960795 + 807807 * 2 ^ 59
def prefixEnd_807807 : Nat := 4983230072969 + 3 ^ 40 * 807807 * 2
def baseEnd_807807 : Nat := 368705126281445497864417

theorem tailTrace_807807 : CollatzResearch.WordTrace tailWord_807807 prefixEnd_807807 368705126281445497864417 := by
  unfold tailWord_807807
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463141784460676296957675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19642094522973784197971783 29463141784460676296957675)
  ·
    refine ⟨44194712676691014445436513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29463141784460676296957675 44194712676691014445436513)
    ·
      refine ⟨33146034507518260834077385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44194712676691014445436513 33146034507518260834077385)
      ·
        refine ⟨24859525880638695625558039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33146034507518260834077385 24859525880638695625558039)
        ·
          refine ⟨37289288820958043438337059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24859525880638695625558039 37289288820958043438337059)
          ·
            refine ⟨55933933231437065157505589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37289288820958043438337059 55933933231437065157505589)
            ·
              refine ⟨5243806240447224858516149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55933933231437065157505589 5243806240447224858516149)
              ·
                refine ⟨491606835041927330485889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5243806240447224858516149 491606835041927330485889)
                ·
                  refine ⟨368705126281445497864417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491606835041927330485889 368705126281445497864417)
                  ·
                    rfl

theorem cell20_807807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 2].length) (baseStart_807807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807807 prefixEnd_807807 := by exact prefixLift 807807
  have htrace : WordTrace (prefixWord ++ tailWord_807807) baseStart_807807 baseEnd_807807 := by
    simpa [prefixWord, tailWord_807807, baseEnd_807807] using wordTrace_append hprefix tailTrace_807807
  have hstable : (prefixWord ++ tailWord_807807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807807).length < 2 ^ (prefixWord ++ tailWord_807807).sum := by decide
  have hdescent : baseEnd_807807 < baseStart_807807 := by decide
  rcases family_descends (prefixWord ++ tailWord_807807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807810 : List Nat := [3, 4, 2, 2, 1, 1, 7]
def baseStart_807810 : Nat := 118140960795 + 807810 * 2 ^ 59
def prefixEnd_807810 : Nat := 4983230072969 + 3 ^ 40 * 807810 * 2
def baseEnd_807810 : Nat := 40967388395910091196045

theorem tailTrace_807810 : CollatzResearch.WordTrace tailWord_807810 prefixEnd_807810 40967388395910091196045 := by
  unfold tailWord_807810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7365812800862451952329221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19642167468966538539544589 7365812800862451952329221)
  ·
    refine ⟨1381089900161709741061729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7365812800862451952329221 1381089900161709741061729)
    ·
      refine ⟨1035817425121282305796297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1381089900161709741061729 1035817425121282305796297)
      ·
        refine ⟨776863068840961729347223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1035817425121282305796297 776863068840961729347223)
        ·
          refine ⟨1165294603261442594020835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776863068840961729347223 1165294603261442594020835)
          ·
            refine ⟨1747941904892163891031253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165294603261442594020835 1747941904892163891031253)
            ·
              refine ⟨40967388395910091196045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1747941904892163891031253 40967388395910091196045)
              ·
                rfl

theorem cell20_807810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 7].length) (baseStart_807810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807810 prefixEnd_807810 := by exact prefixLift 807810
  have htrace : WordTrace (prefixWord ++ tailWord_807810) baseStart_807810 baseEnd_807810 := by
    simpa [prefixWord, tailWord_807810, baseEnd_807810] using wordTrace_append hprefix tailTrace_807810
  have hstable : (prefixWord ++ tailWord_807810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807810).length < 2 ^ (prefixWord ++ tailWord_807810).sum := by decide
  have hdescent : baseEnd_807810 < baseStart_807810 := by decide
  rcases family_descends (prefixWord ++ tailWord_807810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807869 : List Nat := [1, 4, 1, 2, 5, 1, 6]
def baseStart_807869 : Nat := 118140960795 + 807869 * 2 ^ 59
def prefixEnd_807869 : Nat := 4983230072969 + 3 ^ 40 * 807869 * 2
def baseEnd_807869 : Nat := 40970380530094315310833

theorem tailTrace_807869 : CollatzResearch.WordTrace tailWord_807869 prefixEnd_807869 40970380530094315310833 := by
  unfold tailWord_807869
  simp only [CollatzResearch.WordTrace]
  refine ⟨29465403110236060885714661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19643602073490707257143107 29465403110236060885714661)
  ·
    refine ⟨5524763083169261416071499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29465403110236060885714661 5524763083169261416071499)
    ·
      refine ⟨8287144624753892124107249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5524763083169261416071499 8287144624753892124107249)
      ·
        refine ⟨6215358468565419093080437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8287144624753892124107249 6215358468565419093080437)
        ·
          refine ⟨582689856428008039976291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6215358468565419093080437 582689856428008039976291)
          ·
            refine ⟨874034784642012059964437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582689856428008039976291 874034784642012059964437)
            ·
              refine ⟨40970380530094315310833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 874034784642012059964437 40970380530094315310833)
              ·
                rfl

theorem cell20_807869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 6].length) (baseStart_807869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807869 prefixEnd_807869 := by exact prefixLift 807869
  have htrace : WordTrace (prefixWord ++ tailWord_807869) baseStart_807869 baseEnd_807869 := by
    simpa [prefixWord, tailWord_807869, baseEnd_807869] using wordTrace_append hprefix tailTrace_807869
  have hstable : (prefixWord ++ tailWord_807869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807869).length < 2 ^ (prefixWord ++ tailWord_807869).sum := by decide
  have hdescent : baseEnd_807869 < baseStart_807869 := by decide
  rcases family_descends (prefixWord ++ tailWord_807869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807883 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 4]
def baseStart_807883 : Nat := 118140960795 + 807883 * 2 ^ 59
def prefixEnd_807883 : Nat := 4983230072969 + 3 ^ 40 * 807883 * 2
def baseEnd_807883 : Nat := 368739814752327011330773

theorem tailTrace_807883 : CollatzResearch.WordTrace tailWord_807883 prefixEnd_807883 368739814752327011330773 := by
  unfold tailWord_807883
  simp only [CollatzResearch.WordTrace]
  refine ⟨29465913732185341276724303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19643942488123560851149535 29465913732185341276724303)
  ·
    refine ⟨44198870598278011915086455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29465913732185341276724303 44198870598278011915086455)
    ·
      refine ⟨66298305897417017872629683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44198870598278011915086455 66298305897417017872629683)
      ·
        refine ⟨99447458846125526808944525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66298305897417017872629683 99447458846125526808944525)
        ·
          refine ⟨37292797067297072553354197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99447458846125526808944525 37292797067297072553354197)
          ·
            refine ⟨874049931264775137969239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37292797067297072553354197 874049931264775137969239)
            ·
              refine ⟨1311074896897162706953859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874049931264775137969239 1311074896897162706953859)
              ·
                refine ⟨1966612345345744060430789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311074896897162706953859 1966612345345744060430789)
                ·
                  refine ⟨368739814752327011330773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966612345345744060430789 368739814752327011330773)
                  ·
                    rfl

theorem cell20_807883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_807883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807883 prefixEnd_807883 := by exact prefixLift 807883
  have htrace : WordTrace (prefixWord ++ tailWord_807883) baseStart_807883 baseEnd_807883 := by
    simpa [prefixWord, tailWord_807883, baseEnd_807883] using wordTrace_append hprefix tailTrace_807883
  have hstable : (prefixWord ++ tailWord_807883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807883).length < 2 ^ (prefixWord ++ tailWord_807883).sum := by decide
  have hdescent : baseEnd_807883 < baseStart_807883 := by decide
  rcases family_descends (prefixWord ++ tailWord_807883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807885 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 3]
def baseStart_807885 : Nat := 118140960795 + 807885 * 2 ^ 59
def prefixEnd_807885 : Nat := 4983230072969 + 3 ^ 40 * 807885 * 2
def baseEnd_807885 : Nat := 368740727606823893264099

theorem tailTrace_807885 : CollatzResearch.WordTrace tailWord_807885 prefixEnd_807885 368740727606823893264099 := by
  unfold tailWord_807885
  simp only [CollatzResearch.WordTrace]
  refine ⟨29465986678178095618297109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19643991118785397078864739 29465986678178095618297109)
  ·
    refine ⟨1381218125539598232107677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29465986678178095618297109 1381218125539598232107677)
    ·
      refine ⟨517956797077349337040379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1381218125539598232107677 517956797077349337040379)
      ·
        refine ⟨776935195616024005560569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517956797077349337040379 776935195616024005560569)
        ·
          refine ⟨582701396712018004170427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 776935195616024005560569 582701396712018004170427)
          ·
            refine ⟨874052095068027006255641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582701396712018004170427 874052095068027006255641)
            ·
              refine ⟨655539071301020254691731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874052095068027006255641 655539071301020254691731)
              ·
                refine ⟨983308606951530382037597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655539071301020254691731 983308606951530382037597)
                ·
                  refine ⟨368740727606823893264099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983308606951530382037597 368740727606823893264099)
                  ·
                    rfl

theorem cell20_807885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_807885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807885 prefixEnd_807885 := by exact prefixLift 807885
  have htrace : WordTrace (prefixWord ++ tailWord_807885) baseStart_807885 baseEnd_807885 := by
    simpa [prefixWord, tailWord_807885, baseEnd_807885] using wordTrace_append hprefix tailTrace_807885
  have hstable : (prefixWord ++ tailWord_807885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807885).length < 2 ^ (prefixWord ++ tailWord_807885).sum := by decide
  have hdescent : baseEnd_807885 < baseStart_807885 := by decide
  rcases family_descends (prefixWord ++ tailWord_807885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807890 : List Nat := [3, 2, 2, 3, 1, 1, 1, 7]
def baseStart_807890 : Nat := 118140960795 + 807890 * 2 ^ 59
def prefixEnd_807890 : Nat := 4983230072969 + 3 ^ 40 * 807890 * 2
def baseEnd_807890 : Nat := 122914336581022032699137

theorem tailTrace_807890 : CollatzResearch.WordTrace tailWord_807890 prefixEnd_807890 122914336581022032699137 := by
  unfold tailWord_807890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366542260789995368057281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19644112695439987648152749 7366542260789995368057281)
  ·
    refine ⟨5524906695592496526042961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7366542260789995368057281 5524906695592496526042961)
    ·
      refine ⟨4143680021694372394532221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5524906695592496526042961 4143680021694372394532221)
      ·
        refine ⟨1553880008135389647949583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4143680021694372394532221 1553880008135389647949583)
        ·
          refine ⟨2330820012203084471924375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553880008135389647949583 2330820012203084471924375)
          ·
            refine ⟨3496230018304626707886563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330820012203084471924375 3496230018304626707886563)
            ·
              refine ⟨5244345027456940061829845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496230018304626707886563 5244345027456940061829845)
              ·
                refine ⟨122914336581022032699137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5244345027456940061829845 122914336581022032699137)
                ·
                  rfl

theorem cell20_807890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_807890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807890 prefixEnd_807890 := by exact prefixLift 807890
  have htrace : WordTrace (prefixWord ++ tailWord_807890) baseStart_807890 baseEnd_807890 := by
    simpa [prefixWord, tailWord_807890, baseEnd_807890] using wordTrace_append hprefix tailTrace_807890
  have hstable : (prefixWord ++ tailWord_807890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807890).length < 2 ^ (prefixWord ++ tailWord_807890).sum := by decide
  have hdescent : baseEnd_807890 < baseStart_807890 := by decide
  rcases family_descends (prefixWord ++ tailWord_807890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807924 : List Nat := [2, 6, 2, 1, 9]
def baseStart_807924 : Nat := 118140960795 + 807924 * 2 ^ 59
def prefixEnd_807924 : Nat := 4983230072969 + 3 ^ 40 * 807924 * 2
def baseEnd_807924 : Nat := 4552574423080408530419

theorem tailTrace_807924 : CollatzResearch.WordTrace tailWord_807924 prefixEnd_807924 4552574423080408530419 := by
  unfold tailWord_807924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733704562518402639483413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19644939416691203519311217 14733704562518402639483413)
  ·
    refine ⟨690642401368050123725785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14733704562518402639483413 690642401368050123725785)
    ·
      refine ⟨517981801026037592794339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 690642401368050123725785 517981801026037592794339)
      ·
        refine ⟨776972701539056389191509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517981801026037592794339 776972701539056389191509)
        ·
          refine ⟨4552574423080408530419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 776972701539056389191509 4552574423080408530419)
          ·
            rfl

theorem cell20_807924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 9].length) (baseStart_807924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807924 prefixEnd_807924 := by exact prefixLift 807924
  have htrace : WordTrace (prefixWord ++ tailWord_807924) baseStart_807924 baseEnd_807924 := by
    simpa [prefixWord, tailWord_807924, baseEnd_807924] using wordTrace_append hprefix tailTrace_807924
  have hstable : (prefixWord ++ tailWord_807924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807924).length < 2 ^ (prefixWord ++ tailWord_807924).sum := by decide
  have hdescent : baseEnd_807924 < baseStart_807924 := by decide
  rcases family_descends (prefixWord ++ tailWord_807924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807959 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_807959 : Nat := 118140960795 + 807959 * 2 ^ 59
def prefixEnd_807959 : Nat := 4983230072969 + 3 ^ 40 * 807959 * 2
def baseEnd_807959 : Nat := 368774503223208524797129

theorem tailTrace_807959 : CollatzResearch.WordTrace tailWord_807959 prefixEnd_807959 368774503223208524797129 := by
  unfold tailWord_807959
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468685679910006256490931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19645790453273337504327287 29468685679910006256490931)
  ·
    refine ⟨44203028519865009384736397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29468685679910006256490931 44203028519865009384736397)
    ·
      refine ⟨16576135694949378519276149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44203028519865009384736397 16576135694949378519276149)
      ·
        refine ⟨1554012721401504236182139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16576135694949378519276149 1554012721401504236182139)
        ·
          refine ⟨2331019082102256354273209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554012721401504236182139 2331019082102256354273209)
          ·
            refine ⟨1748264311576692265704907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2331019082102256354273209 1748264311576692265704907)
            ·
              refine ⟨2622396467365038398557361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748264311576692265704907 2622396467365038398557361)
              ·
                refine ⟨1966797350523778798918021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622396467365038398557361 1966797350523778798918021)
                ·
                  refine ⟨368774503223208524797129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966797350523778798918021 368774503223208524797129)
                  ·
                    rfl

theorem cell20_807959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_807959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807959 prefixEnd_807959 := by exact prefixLift 807959
  have htrace : WordTrace (prefixWord ++ tailWord_807959) baseStart_807959 baseEnd_807959 := by
    simpa [prefixWord, tailWord_807959, baseEnd_807959] using wordTrace_append hprefix tailTrace_807959
  have hstable : (prefixWord ++ tailWord_807959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807959).length < 2 ^ (prefixWord ++ tailWord_807959).sum := by decide
  have hdescent : baseEnd_807959 < baseStart_807959 := by decide
  rcases family_descends (prefixWord ++ tailWord_807959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807990 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_807990 : Nat := 118140960795 + 807990 * 2 ^ 59
def prefixEnd_807990 : Nat := 4983230072969 + 3 ^ 40 * 807990 * 2
def baseEnd_807990 : Nat := 368788652467910194763669

theorem tailTrace_807990 : CollatzResearch.WordTrace tailWord_807990 prefixEnd_807990 368788652467910194763669 := by
  unfold tailWord_807990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841863521424856159429339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19646544228531799033912949 1841863521424856159429339)
  ·
    refine ⟨2762795282137284239144009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1841863521424856159429339 2762795282137284239144009)
    ·
      refine ⟨2072096461602963179358007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2762795282137284239144009 2072096461602963179358007)
      ·
        refine ⟨3108144692404444769037011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072096461602963179358007 3108144692404444769037011)
        ·
          refine ⟨4662217038606667153555517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108144692404444769037011 4662217038606667153555517)
          ·
            refine ⟨1748331389477500182583319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4662217038606667153555517 1748331389477500182583319)
            ·
              refine ⟨2622497084216250273874979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748331389477500182583319 2622497084216250273874979)
              ·
                refine ⟨3933745626324375410812469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622497084216250273874979 3933745626324375410812469)
                ·
                  refine ⟨368788652467910194763669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3933745626324375410812469 368788652467910194763669)
                  ·
                    rfl

theorem cell20_807990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_807990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807990 prefixEnd_807990 := by exact prefixLift 807990
  have htrace : WordTrace (prefixWord ++ tailWord_807990) baseStart_807990 baseEnd_807990 := by
    simpa [prefixWord, tailWord_807990, baseEnd_807990] using wordTrace_append hprefix tailTrace_807990
  have hstable : (prefixWord ++ tailWord_807990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807990).length < 2 ^ (prefixWord ++ tailWord_807990).sum := by decide
  have hdescent : baseEnd_807990 < baseStart_807990 := by decide
  rcases family_descends (prefixWord ++ tailWord_807990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807997 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_807997 : Nat := 118140960795 + 807997 * 2 ^ 59
def prefixEnd_807997 : Nat := 4983230072969 + 3 ^ 40 * 807997 * 2
def baseEnd_807997 : Nat := 368791847458649281530307

theorem tailTrace_807997 : CollatzResearch.WordTrace tailWord_807997 prefixEnd_807997 368791847458649281530307 := by
  unfold tailWord_807997
  simp only [CollatzResearch.WordTrace]
  refine ⟨29470071653772338746374245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19646714435848225830916163 29470071653772338746374245)
  ·
    refine ⟨5525638435082313514945171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29470071653772338746374245 5525638435082313514945171)
    ·
      refine ⟨8288457652623470272417757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5525638435082313514945171 8288457652623470272417757)
      ·
        refine ⟨3108171619733801352156659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8288457652623470272417757 3108171619733801352156659)
        ·
          refine ⟨4662257429600702028234989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108171619733801352156659 4662257429600702028234989)
          ·
            refine ⟨1748346536100263260588121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4662257429600702028234989 1748346536100263260588121)
            ·
              refine ⟨1311259902075197445441091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748346536100263260588121 1311259902075197445441091)
              ·
                refine ⟨1966889853112796168161637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311259902075197445441091 1966889853112796168161637)
                ·
                  refine ⟨368791847458649281530307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966889853112796168161637 368791847458649281530307)
                  ·
                    rfl

theorem cell20_807997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_807997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_807997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_807997 prefixEnd_807997 := by exact prefixLift 807997
  have htrace : WordTrace (prefixWord ++ tailWord_807997) baseStart_807997 baseEnd_807997 := by
    simpa [prefixWord, tailWord_807997, baseEnd_807997] using wordTrace_append hprefix tailTrace_807997
  have hstable : (prefixWord ++ tailWord_807997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807997).length < 2 ^ (prefixWord ++ tailWord_807997).sum := by decide
  have hdescent : baseEnd_807997 < baseStart_807997 := by decide
  rcases family_descends (prefixWord ++ tailWord_807997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808032 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_808032 : Nat := 118140960795 + 808032 * 2 ^ 59
def prefixEnd_808032 : Nat := 4983230072969 + 3 ^ 40 * 808032 * 2
def baseEnd_808032 : Nat := 368807822412344715363497

theorem tailTrace_808032 : CollatzResearch.WordTrace tailWord_808032 prefixEnd_808032 368807822412344715363497 := by
  unfold tailWord_808032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735674104322769861949175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19647565472430359815932233 14735674104322769861949175)
  ·
    refine ⟨22103511156484154792923763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14735674104322769861949175 22103511156484154792923763)
    ·
      refine ⟨33155266734726232189385645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22103511156484154792923763 33155266734726232189385645)
      ·
        refine ⟨12433225025522337071019617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33155266734726232189385645 12433225025522337071019617)
        ·
          refine ⟨9324918769141752803264713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12433225025522337071019617 9324918769141752803264713)
          ·
            refine ⟨6993689076856314602448535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9324918769141752803264713 6993689076856314602448535)
            ·
              refine ⟨10490533615284471903672803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993689076856314602448535 10490533615284471903672803)
              ·
                refine ⟨15735800422926707855509205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10490533615284471903672803 15735800422926707855509205)
                ·
                  refine ⟨368807822412344715363497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15735800422926707855509205 368807822412344715363497)
                  ·
                    rfl

theorem cell20_808032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_808032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808032 prefixEnd_808032 := by exact prefixLift 808032
  have htrace : WordTrace (prefixWord ++ tailWord_808032) baseStart_808032 baseEnd_808032 := by
    simpa [prefixWord, tailWord_808032, baseEnd_808032] using wordTrace_append hprefix tailTrace_808032
  have hstable : (prefixWord ++ tailWord_808032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808032).length < 2 ^ (prefixWord ++ tailWord_808032).sum := by decide
  have hdescent : baseEnd_808032 < baseStart_808032 := by decide
  rcases family_descends (prefixWord ++ tailWord_808032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808042 : List Nat := [3, 1, 3, 2, 2, 3, 6]
def baseStart_808042 : Nat := 118140960795 + 808042 * 2 ^ 59
def prefixEnd_808042 : Nat := 4983230072969 + 3 ^ 40 * 808042 * 2
def baseEnd_808042 : Nat := 40979154076092125003347

theorem tailTrace_808042 : CollatzResearch.WordTrace tailWord_808042 prefixEnd_808042 40979154076092125003347 := by
  unfold tailWord_808042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367928234652327857940595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19647808625739540954508253 7367928234652327857940595)
  ·
    refine ⟨11051892351978491786910893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7367928234652327857940595 11051892351978491786910893)
    ·
      refine ⟨4144459631991934420091585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11051892351978491786910893 4144459631991934420091585)
      ·
        refine ⟨3108344723993950815068689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4144459631991934420091585 3108344723993950815068689)
        ·
          refine ⟨2331258542995463111301517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3108344723993950815068689 2331258542995463111301517)
          ·
            refine ⟨874221953623298666738069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2331258542995463111301517 874221953623298666738069)
            ·
              refine ⟨40979154076092125003347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 874221953623298666738069 40979154076092125003347)
              ·
                rfl

theorem cell20_808042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 6].length) (baseStart_808042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808042 prefixEnd_808042 := by exact prefixLift 808042
  have htrace : WordTrace (prefixWord ++ tailWord_808042) baseStart_808042 baseEnd_808042 := by
    simpa [prefixWord, tailWord_808042, baseEnd_808042] using wordTrace_append hprefix tailTrace_808042
  have hstable : (prefixWord ++ tailWord_808042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808042).length < 2 ^ (prefixWord ++ tailWord_808042).sum := by decide
  have hdescent : baseEnd_808042 < baseStart_808042 := by decide
  rcases family_descends (prefixWord ++ tailWord_808042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808056 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_808056 : Nat := 118140960795 + 808056 * 2 ^ 59
def prefixEnd_808056 : Nat := 4983230072969 + 3 ^ 40 * 808056 * 2
def baseEnd_808056 : Nat := 368818776666307298563399

theorem tailTrace_808056 : CollatzResearch.WordTrace tailWord_808056 prefixEnd_808056 368818776666307298563399 := by
  unfold tailWord_808056
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736111780279295911386011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19648149040372394548514681 14736111780279295911386011)
  ·
    refine ⟨22104167670418943867079017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14736111780279295911386011 22104167670418943867079017)
    ·
      refine ⟨16578125752814207900309263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22104167670418943867079017 16578125752814207900309263)
      ·
        refine ⟨24867188629221311850463895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16578125752814207900309263 24867188629221311850463895)
        ·
          refine ⟨37300782943831967775695843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24867188629221311850463895 37300782943831967775695843)
          ·
            refine ⟨55951174415747951663543765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37300782943831967775695843 55951174415747951663543765)
            ·
              refine ⟨1311355650369092617114307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55951174415747951663543765 1311355650369092617114307)
              ·
                refine ⟨1967033475553638925671461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311355650369092617114307 1967033475553638925671461)
                ·
                  refine ⟨368818776666307298563399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967033475553638925671461 368818776666307298563399)
                  ·
                    rfl

theorem cell20_808056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_808056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808056 prefixEnd_808056 := by exact prefixLift 808056
  have htrace : WordTrace (prefixWord ++ tailWord_808056) baseStart_808056 baseEnd_808056 := by
    simpa [prefixWord, tailWord_808056, baseEnd_808056] using wordTrace_append hprefix tailTrace_808056
  have hstable : (prefixWord ++ tailWord_808056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808056).length < 2 ^ (prefixWord ++ tailWord_808056).sum := by decide
  have hdescent : baseEnd_808056 < baseStart_808056 := by decide
  rcases family_descends (prefixWord ++ tailWord_808056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808125 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 3]
def baseStart_808125 : Nat := 118140960795 + 808125 * 2 ^ 59
def prefixEnd_808125 : Nat := 4983230072969 + 3 ^ 40 * 808125 * 2
def baseEnd_808125 : Nat := 368850270146449725263117

theorem tailTrace_808125 : CollatzResearch.WordTrace tailWord_808125 prefixEnd_808125 368850270146449725263117 := by
  unfold tailWord_808125
  simp only [CollatzResearch.WordTrace]
  refine ⟨29474740197308616607033829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19649826798205744404689219 29474740197308616607033829)
  ·
    refine ⟨5526513786995365613818843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29474740197308616607033829 5526513786995365613818843)
    ·
      refine ⟨8289770680493048420728265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5526513786995365613818843 8289770680493048420728265)
      ·
        refine ⟨6217328010369786315546199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8289770680493048420728265 6217328010369786315546199)
        ·
          refine ⟨9325992015554679473319299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217328010369786315546199 9325992015554679473319299)
          ·
            refine ⟨13988988023332019209978949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9325992015554679473319299 13988988023332019209978949)
            ·
              refine ⟨2622935254374753601871053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13988988023332019209978949 2622935254374753601871053)
              ·
                refine ⟨983600720390532600701645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2622935254374753601871053 983600720390532600701645)
                ·
                  refine ⟨368850270146449725263117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983600720390532600701645 368850270146449725263117)
                  ·
                    rfl

theorem cell20_808125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_808125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808125 prefixEnd_808125 := by exact prefixLift 808125
  have htrace : WordTrace (prefixWord ++ tailWord_808125) baseStart_808125 baseEnd_808125 := by
    simpa [prefixWord, tailWord_808125, baseEnd_808125] using wordTrace_append hprefix tailTrace_808125
  have hstable : (prefixWord ++ tailWord_808125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808125).length < 2 ^ (prefixWord ++ tailWord_808125).sum := by decide
  have hdescent : baseEnd_808125 < baseStart_808125 := by decide
  rcases family_descends (prefixWord ++ tailWord_808125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808153 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_808153 : Nat := 118140960795 + 808153 * 2 ^ 59
def prefixEnd_808153 : Nat := 4983230072969 + 3 ^ 40 * 808153 * 2
def baseEnd_808153 : Nat := 368863050109406072329669

theorem tailTrace_808153 : CollatzResearch.WordTrace tailWord_808153 prefixEnd_808153 368863050109406072329669 := by
  unfold tailWord_808153
  simp only [CollatzResearch.WordTrace]
  refine ⟨29475761441207177389053113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19650507627471451592702075 29475761441207177389053113)
  ·
    refine ⟨22106821080905383041789835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29475761441207177389053113 22106821080905383041789835)
    ·
      refine ⟨33160231621358074562684753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22106821080905383041789835 33160231621358074562684753)
      ·
        refine ⟨24870173716018555922013565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33160231621358074562684753 24870173716018555922013565)
        ·
          refine ⟨9326315143506958470755087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24870173716018555922013565 9326315143506958470755087)
          ·
            refine ⟨13989472715260437706132631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326315143506958470755087 13989472715260437706132631)
            ·
              refine ⟨20984209072890656559198947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13989472715260437706132631 20984209072890656559198947)
              ·
                refine ⟨31476313609335984838798421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20984209072890656559198947 31476313609335984838798421)
                ·
                  refine ⟨368863050109406072329669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31476313609335984838798421 368863050109406072329669)
                  ·
                    rfl

theorem cell20_808153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_808153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808153 prefixEnd_808153 := by exact prefixLift 808153
  have htrace : WordTrace (prefixWord ++ tailWord_808153) baseStart_808153 baseEnd_808153 := by
    simpa [prefixWord, tailWord_808153, baseEnd_808153] using wordTrace_append hprefix tailTrace_808153
  have hstable : (prefixWord ++ tailWord_808153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808153).length < 2 ^ (prefixWord ++ tailWord_808153).sum := by decide
  have hdescent : baseEnd_808153 < baseStart_808153 := by decide
  rcases family_descends (prefixWord ++ tailWord_808153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808170 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_808170 : Nat := 118140960795 + 808170 * 2 ^ 59
def prefixEnd_808170 : Nat := 4983230072969 + 3 ^ 40 * 808170 * 2
def baseEnd_808170 : Nat := 368870809372629568762933

theorem tailTrace_808170 : CollatzResearch.WordTrace tailWord_808170 prefixEnd_808170 368870809372629568762933 := by
  unfold tailWord_808170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369095370536397323105491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19650920988097059528281309 7369095370536397323105491)
  ·
    refine ⟨11053643055804595984658237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7369095370536397323105491 11053643055804595984658237)
    ·
      refine ⟨4145116145926723494246839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11053643055804595984658237 4145116145926723494246839)
      ·
        refine ⟨6217674218890085241370259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145116145926723494246839 6217674218890085241370259)
        ·
          refine ⟨9326511328335127862055389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217674218890085241370259 9326511328335127862055389)
          ·
            refine ⟨3497441748125672948270771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9326511328335127862055389 3497441748125672948270771)
            ·
              refine ⟨5246162622188509422406157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497441748125672948270771 5246162622188509422406157)
              ·
                refine ⟨1967310983320691033402309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5246162622188509422406157 1967310983320691033402309)
                ·
                  refine ⟨368870809372629568762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967310983320691033402309 368870809372629568762933)
                  ·
                    rfl

theorem cell20_808170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_808170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808170 prefixEnd_808170 := by exact prefixLift 808170
  have htrace : WordTrace (prefixWord ++ tailWord_808170) baseStart_808170 baseEnd_808170 := by
    simpa [prefixWord, tailWord_808170, baseEnd_808170] using wordTrace_append hprefix tailTrace_808170
  have hstable : (prefixWord ++ tailWord_808170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808170).length < 2 ^ (prefixWord ++ tailWord_808170).sum := by decide
  have hdescent : baseEnd_808170 < baseStart_808170 := by decide
  rcases family_descends (prefixWord ++ tailWord_808170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808204 : List Nat := [2, 2, 1, 2, 2, 5, 1, 3, 2]
def baseStart_808204 : Nat := 118140960795 + 808204 * 2 ^ 59
def prefixEnd_808204 : Nat := 4983230072969 + 3 ^ 40 * 808204 * 2
def baseEnd_808204 : Nat := 368886327899076561629461

theorem tailTrace_808204 : CollatzResearch.WordTrace tailWord_808204 prefixEnd_808204 368886327899076561629461 := by
  unfold tailWord_808204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14738810782011206549579833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19651747709348275399439777 14738810782011206549579833)
  ·
    refine ⟨11054108086508404912184875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14738810782011206549579833 11054108086508404912184875)
    ·
      refine ⟨16581162129762607368277313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11054108086508404912184875 16581162129762607368277313)
      ·
        refine ⟨12435871597321955526207985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16581162129762607368277313 12435871597321955526207985)
        ·
          refine ⟨9326903697991466644655989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12435871597321955526207985 9326903697991466644655989)
          ·
            refine ⟨874397221686699997936499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9326903697991466644655989 874397221686699997936499)
            ·
              refine ⟨1311595832530049996904749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874397221686699997936499 1311595832530049996904749)
              ·
                refine ⟨491848437198768748839281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1311595832530049996904749 491848437198768748839281)
                ·
                  refine ⟨368886327899076561629461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491848437198768748839281 368886327899076561629461)
                  ·
                    rfl

theorem cell20_808204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_808204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_808204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_808204 prefixEnd_808204 := by exact prefixLift 808204
  have htrace : WordTrace (prefixWord ++ tailWord_808204) baseStart_808204 baseEnd_808204 := by
    simpa [prefixWord, tailWord_808204, baseEnd_808204] using wordTrace_append hprefix tailTrace_808204
  have hstable : (prefixWord ++ tailWord_808204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808204).length < 2 ^ (prefixWord ++ tailWord_808204).sum := by decide
  have hdescent : baseEnd_808204 < baseStart_808204 := by decide
  rcases family_descends (prefixWord ++ tailWord_808204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
