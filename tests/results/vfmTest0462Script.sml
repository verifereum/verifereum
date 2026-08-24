Theory vfmTest0462[no_sig_docs]
Ancestors vfmTestDefs0462
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0462_0.nsv", "result0462_1.nsv", "result0462_2.nsv"];
val thyn = "vfmTestDefs0462";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
