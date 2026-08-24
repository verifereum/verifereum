Theory vfmTest1139[no_sig_docs]
Ancestors vfmTestDefs1139
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1139_0.nsv", "result1139_1.nsv"];
val thyn = "vfmTestDefs1139";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
