Theory vfmTest2928[no_sig_docs]
Ancestors vfmTestDefs2928
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2928_0.nsv", "result2928_1.nsv", "result2928_2.nsv", "result2928_3.nsv", "result2928_4.nsv", "result2928_5.nsv", "result2928_6.nsv", "result2928_7.nsv", "result2928_8.nsv", "result2928_9.nsv", "result2928_10.nsv"];
val thyn = "vfmTestDefs2928";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
