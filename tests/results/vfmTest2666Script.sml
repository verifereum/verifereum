Theory vfmTest2666[no_sig_docs]
Ancestors vfmTestDefs2666
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2666_0.nsv", "result2666_1.nsv", "result2666_2.nsv", "result2666_3.nsv"];
val thyn = "vfmTestDefs2666";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
