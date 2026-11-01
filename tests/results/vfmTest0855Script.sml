Theory vfmTest0855[no_sig_docs]
Ancestors vfmTestDefs0855
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0855_0.nsv", "result0855_1.nsv", "result0855_2.nsv", "result0855_3.nsv", "result0855_4.nsv", "result0855_5.nsv"];
val thyn = "vfmTestDefs0855";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
