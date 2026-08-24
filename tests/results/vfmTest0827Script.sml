Theory vfmTest0827[no_sig_docs]
Ancestors vfmTestDefs0827
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0827_0.nsv", "result0827_1.nsv", "result0827_2.nsv"];
val thyn = "vfmTestDefs0827";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
