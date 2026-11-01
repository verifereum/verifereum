Theory vfmTest2644[no_sig_docs]
Ancestors vfmTestDefs2644
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2644_0.nsv", "result2644_1.nsv", "result2644_2.nsv", "result2644_3.nsv"];
val thyn = "vfmTestDefs2644";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
