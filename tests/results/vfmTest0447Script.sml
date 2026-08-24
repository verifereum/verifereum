Theory vfmTest0447[no_sig_docs]
Ancestors vfmTestDefs0447
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0447_0.nsv", "result0447_1.nsv", "result0447_2.nsv", "result0447_3.nsv"];
val thyn = "vfmTestDefs0447";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
