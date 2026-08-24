Theory vfmTest0840[no_sig_docs]
Ancestors vfmTestDefs0840
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0840_0.nsv", "result0840_1.nsv"];
val thyn = "vfmTestDefs0840";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
