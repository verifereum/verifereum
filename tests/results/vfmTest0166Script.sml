Theory vfmTest0166[no_sig_docs]
Ancestors vfmTestDefs0166
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0166_0.nsv", "result0166_1.nsv", "result0166_2.nsv", "result0166_3.nsv"];
val thyn = "vfmTestDefs0166";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
