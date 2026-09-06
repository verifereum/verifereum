Theory vfmTest2265[no_sig_docs]
Ancestors vfmTestDefs2265
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2265_0.nsv", "result2265_1.nsv", "result2265_2.nsv", "result2265_3.nsv", "result2265_4.nsv"];
val thyn = "vfmTestDefs2265";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
