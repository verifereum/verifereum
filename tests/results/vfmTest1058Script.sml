Theory vfmTest1058[no_sig_docs]
Ancestors vfmTestDefs1058
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1058_0.nsv", "result1058_1.nsv", "result1058_2.nsv", "result1058_3.nsv"];
val thyn = "vfmTestDefs1058";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
