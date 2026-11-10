Theory vfmTest3115[no_sig_docs]
Ancestors vfmTestDefs3115
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3115_0.nsv", "result3115_1.nsv", "result3115_2.nsv", "result3115_3.nsv", "result3115_4.nsv", "result3115_5.nsv", "result3115_6.nsv", "result3115_7.nsv", "result3115_8.nsv", "result3115_9.nsv", "result3115_10.nsv", "result3115_11.nsv", "result3115_12.nsv", "result3115_13.nsv", "result3115_14.nsv", "result3115_15.nsv"];
val thyn = "vfmTestDefs3115";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
