Theory vfmTest0873[no_sig_docs]
Ancestors vfmTestDefs0873
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0873_0.nsv", "result0873_1.nsv", "result0873_2.nsv", "result0873_3.nsv"];
val thyn = "vfmTestDefs0873";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
