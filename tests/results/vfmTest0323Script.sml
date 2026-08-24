Theory vfmTest0323[no_sig_docs]
Ancestors vfmTestDefs0323
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0323_0.nsv", "result0323_1.nsv"];
val thyn = "vfmTestDefs0323";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
