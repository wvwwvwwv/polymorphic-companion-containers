#[cfg(test)]
mod tests {
    use pcc::CompanionStack;

    #[test]
    fn dynamic_buffers() {
        fn determine_size(data: &[u8]) -> usize {
            data.iter().fold(0, |acc, d| acc + usize::from(*d))
        }

        fn use_buffer_recursive(
            buffer: &mut [u8],
            acc: usize,
            dyn_stack: &mut CompanionStack,
        ) -> usize {
            if buffer.is_empty() {
                return acc;
            }
            let mut ref_mut_new_buffer = dyn_stack.push_slice(&buffer[1..]).unwrap();
            let (new_buffer, dyn_stack) = ref_mut_new_buffer.retrieve_stack();
            use_buffer_recursive(new_buffer, acc + buffer.len(), dyn_stack)
        }

        let data_emulated: [u8; 5] = [2; 5];

        let mut dyn_stack = CompanionStack::default();

        // The size of the buffer is determined at runtime.
        let required_size = determine_size(&data_emulated);

        // The buffer is allocated on the stack.
        let mut ref_mut_buffer = dyn_stack
            .push_many(|_| Ok::<_, ()>(0), required_size)
            .unwrap();

        // The stack can still be used after allocating the buffer.
        let (buffer, dyn_stack) = ref_mut_buffer.retrieve_stack();
        let result = use_buffer_recursive(buffer, 0, dyn_stack);

        assert_eq!(result, 55);
    }
}
