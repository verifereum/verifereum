Theory vfmTest0321[no_sig_docs]
Ancestors vfmTestDefs0321
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0321_0.nsv", "result0321_1.nsv", "result0321_2.nsv", "result0321_3.nsv", "result0321_4.nsv", "result0321_5.nsv", "result0321_6.nsv", "result0321_7.nsv"];
val thyn = "vfmTestDefs0321";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
