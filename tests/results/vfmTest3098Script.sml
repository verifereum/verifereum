Theory vfmTest3098[no_sig_docs]
Ancestors vfmTestDefs3098
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3098_0.nsv", "result3098_1.nsv"];
val thyn = "vfmTestDefs3098";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
