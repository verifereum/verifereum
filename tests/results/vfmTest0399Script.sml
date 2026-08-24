Theory vfmTest0399[no_sig_docs]
Ancestors vfmTestDefs0399
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0399_0.nsv", "result0399_1.nsv", "result0399_2.nsv", "result0399_3.nsv", "result0399_4.nsv", "result0399_5.nsv"];
val thyn = "vfmTestDefs0399";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
