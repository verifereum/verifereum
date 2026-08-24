Theory vfmTest0038[no_sig_docs]
Ancestors vfmTestDefs0038
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0038_0.nsv", "result0038_1.nsv", "result0038_2.nsv", "result0038_3.nsv", "result0038_4.nsv"];
val thyn = "vfmTestDefs0038";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
