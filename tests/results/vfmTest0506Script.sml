Theory vfmTest0506[no_sig_docs]
Ancestors vfmTestDefs0506
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0506_0.nsv", "result0506_1.nsv"];
val thyn = "vfmTestDefs0506";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
