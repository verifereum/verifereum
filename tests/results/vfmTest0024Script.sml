Theory vfmTest0024[no_sig_docs]
Ancestors vfmTestDefs0024
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0024_0.nsv", "result0024_1.nsv", "result0024_2.nsv"];
val thyn = "vfmTestDefs0024";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
