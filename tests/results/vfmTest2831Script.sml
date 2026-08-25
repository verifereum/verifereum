Theory vfmTest2831[no_sig_docs]
Ancestors vfmTestDefs2831
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2831_0.nsv", "result2831_1.nsv", "result2831_2.nsv", "result2831_3.nsv"];
val thyn = "vfmTestDefs2831";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
