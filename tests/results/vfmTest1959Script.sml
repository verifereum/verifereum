Theory vfmTest1959[no_sig_docs]
Ancestors vfmTestDefs1959
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1959_0.nsv", "result1959_1.nsv", "result1959_2.nsv", "result1959_3.nsv", "result1959_4.nsv", "result1959_5.nsv", "result1959_6.nsv", "result1959_7.nsv"];
val thyn = "vfmTestDefs1959";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
