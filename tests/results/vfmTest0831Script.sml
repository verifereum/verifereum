Theory vfmTest0831[no_sig_docs]
Ancestors vfmTestDefs0831
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0831_0.nsv", "result0831_1.nsv"];
val thyn = "vfmTestDefs0831";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
