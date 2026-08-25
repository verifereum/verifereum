Theory vfmTest2585[no_sig_docs]
Ancestors vfmTestDefs2585
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2585_0.nsv", "result2585_1.nsv", "result2585_2.nsv", "result2585_3.nsv", "result2585_4.nsv"];
val thyn = "vfmTestDefs2585";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
