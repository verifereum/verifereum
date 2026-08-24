Theory vfmTest2609[no_sig_docs]
Ancestors vfmTestDefs2609
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2609_0.nsv", "result2609_1.nsv", "result2609_2.nsv", "result2609_3.nsv"];
val thyn = "vfmTestDefs2609";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
