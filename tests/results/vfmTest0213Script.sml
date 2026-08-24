Theory vfmTest0213[no_sig_docs]
Ancestors vfmTestDefs0213
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0213_0.nsv", "result0213_1.nsv"];
val thyn = "vfmTestDefs0213";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
