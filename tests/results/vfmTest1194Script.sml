Theory vfmTest1194[no_sig_docs]
Ancestors vfmTestDefs1194
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1194_0.nsv", "result1194_1.nsv", "result1194_2.nsv", "result1194_3.nsv", "result1194_4.nsv", "result1194_5.nsv"];
val thyn = "vfmTestDefs1194";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
