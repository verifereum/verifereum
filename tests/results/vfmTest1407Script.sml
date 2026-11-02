Theory vfmTest1407[no_sig_docs]
Ancestors vfmTestDefs1407
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1407_0.nsv", "result1407_1.nsv", "result1407_2.nsv", "result1407_3.nsv", "result1407_4.nsv", "result1407_5.nsv", "result1407_6.nsv", "result1407_7.nsv", "result1407_8.nsv", "result1407_9.nsv"];
val thyn = "vfmTestDefs1407";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
