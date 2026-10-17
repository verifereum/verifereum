Theory vfmTest1619[no_sig_docs]
Ancestors vfmTestDefs1619
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1619_0.nsv", "result1619_1.nsv", "result1619_2.nsv", "result1619_3.nsv", "result1619_4.nsv", "result1619_5.nsv", "result1619_6.nsv", "result1619_7.nsv"];
val thyn = "vfmTestDefs1619";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
