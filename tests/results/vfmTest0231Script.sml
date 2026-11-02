Theory vfmTest0231[no_sig_docs]
Ancestors vfmTestDefs0231
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0231_0.nsv", "result0231_1.nsv", "result0231_2.nsv", "result0231_3.nsv", "result0231_4.nsv", "result0231_5.nsv", "result0231_6.nsv", "result0231_7.nsv"];
val thyn = "vfmTestDefs0231";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
