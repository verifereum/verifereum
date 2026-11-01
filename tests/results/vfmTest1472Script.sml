Theory vfmTest1472[no_sig_docs]
Ancestors vfmTestDefs1472
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1472_0.nsv", "result1472_1.nsv", "result1472_2.nsv", "result1472_3.nsv", "result1472_4.nsv", "result1472_5.nsv", "result1472_6.nsv", "result1472_7.nsv"];
val thyn = "vfmTestDefs1472";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
