Theory vfmTest0303[no_sig_docs]
Ancestors vfmTestDefs0303
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0303_0.nsv", "result0303_1.nsv", "result0303_2.nsv", "result0303_3.nsv"];
val thyn = "vfmTestDefs0303";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
