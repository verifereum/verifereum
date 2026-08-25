Theory vfmTest0793[no_sig_docs]
Ancestors vfmTestDefs0793
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0793_0.nsv", "result0793_1.nsv", "result0793_2.nsv", "result0793_3.nsv", "result0793_4.nsv", "result0793_5.nsv", "result0793_6.nsv", "result0793_7.nsv", "result0793_8.nsv", "result0793_9.nsv", "result0793_10.nsv", "result0793_11.nsv", "result0793_12.nsv", "result0793_13.nsv", "result0793_14.nsv", "result0793_15.nsv", "result0793_16.nsv", "result0793_17.nsv", "result0793_18.nsv", "result0793_19.nsv", "result0793_20.nsv", "result0793_21.nsv", "result0793_22.nsv", "result0793_23.nsv"];
val thyn = "vfmTestDefs0793";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
