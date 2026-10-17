Theory vfmTest0252[no_sig_docs]
Ancestors vfmTestDefs0252
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0252_0.nsv", "result0252_1.nsv", "result0252_2.nsv", "result0252_3.nsv", "result0252_4.nsv", "result0252_5.nsv", "result0252_6.nsv", "result0252_7.nsv", "result0252_8.nsv", "result0252_9.nsv", "result0252_10.nsv", "result0252_11.nsv", "result0252_12.nsv", "result0252_13.nsv", "result0252_14.nsv", "result0252_15.nsv", "result0252_16.nsv", "result0252_17.nsv", "result0252_18.nsv", "result0252_19.nsv", "result0252_20.nsv"];
val thyn = "vfmTestDefs0252";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
